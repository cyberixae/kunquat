

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010-2014
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>
#include <inttypes.h>
#include <limits.h>
#include <string.h>
#include <math.h>

#include <containers/AAtree.h>
#include <Connections.h>
#include <debug/assert.h>
#include <Device_node.h>
#include <devices/DSP_table.h>
#include <devices/Effect.h>
#include <memory.h>
#include <string/common.h>


struct Connections
{
    AAtree* nodes;
    AAiter* iter;
};


/**
 * Resets the graph for searching purposes.
 *
 * \param graph   The Connections -- must not be \c NULL.
 */
static void Connections_reset(Connections* graph);


/**
 * Tells whether there is a cycle inside Connections.
 *
 * All Connections must be acyclic.
 *
 * \param graph   The Connections -- must not be \c NULL.
 *
 * \return   \c true if there is a cycle in \a graph, otherwise \c false.
 */
static bool Connections_is_cyclic(Connections* graph);


/**
 * Validates a connection path.
 *
 * This function also strips the port directory off the path.
 *
 * \param str     The path -- must not be \c NULL.
 * \param level   The connection level -- must be valid.
 * \param type    The type of the path -- must be valid.
 * \param state   The Read state -- must not be \c NULL.
 *
 * \return   The port number if the path is valid, otherwise \c -1.
 */
static int validate_connection_path(
        Streader* sr,
        char* str,
        Connection_level level,
        Device_port_type type);


#define mem_error_if(expr, graph, node, sr)                           \
    if (true)                                                         \
    {                                                                 \
        if ((expr))                                                   \
        {                                                             \
            Streader_set_memory_error(                                \
                    sr, "Could not allocate memory for connections"); \
            del_Device_node(node);                                    \
            del_Connections(graph);                                   \
            return NULL;                                              \
        }                                                             \
    } else (void)0

typedef struct read_conn_data
{
    Connections* graph;
    Connection_level level;
    Ins_table* insts;
    Effect_table* effects;
    const DSP_table* dsps;
    Device* master;
} read_conn_data;

static bool read_connection(Streader* sr, int32_t index, void* userdata)
{
    assert(sr != NULL);
    (void)index;
    assert(userdata != NULL);

    read_conn_data* rcdata = userdata;

    char src_name[KQT_DEVICE_NODE_NAME_MAX] = "";
    char dest_name[KQT_DEVICE_NODE_NAME_MAX] = "";
    if (!Streader_readf(
                sr,
                "[%s,%s]",
                KQT_DEVICE_NODE_NAME_MAX, src_name,
                KQT_DEVICE_NODE_NAME_MAX, dest_name))
        return false;

    int src_port = validate_connection_path(
            sr,
            src_name,
            rcdata->level,
            DEVICE_PORT_TYPE_SEND);
    int dest_port = validate_connection_path(
            sr,
            dest_name,
            rcdata->level,
            DEVICE_PORT_TYPE_RECEIVE);
    if (Streader_is_error_set(sr))
        return false;

    if ((rcdata->level & CONNECTION_LEVEL_EFFECT))
    {
        if (string_eq(src_name, ""))
            strcpy(src_name, "Iin");
    }

    if (AAtree_get_exact(rcdata->graph->nodes, src_name) == NULL)
    {
        const Device* actual_master = rcdata->master;
        if ((rcdata->level & CONNECTION_LEVEL_EFFECT) &&
                string_eq(src_name, "Iin"))
            actual_master = Effect_get_input_interface((Effect*)rcdata->master);

        Device_node* new_src = new_Device_node(
                src_name,
                rcdata->insts,
                rcdata->effects,
                rcdata->dsps,
                actual_master);

        mem_error_if(new_src == NULL, rcdata->graph, NULL, sr);
        mem_error_if(
                !AAtree_ins(rcdata->graph->nodes, new_src),
                rcdata->graph,
                new_src,
                sr);
    }
    Device_node* src_node = AAtree_get_exact(rcdata->graph->nodes, src_name);

    if (AAtree_get_exact(rcdata->graph->nodes, dest_name) == NULL)
    {
#if 0
        Device* actual_master = rcdata->master;
        if ((rcdata->level & CONNECTION_LEVEL_EFFECT) &&
                string_eq(dest_name, ""))
        {
            actual_master = Effect_get_output_interface((Effect*)rcdata->master);
        }
#endif
        Device_node* new_dest = new_Device_node(
                dest_name,
                rcdata->insts,
                rcdata->effects,
                rcdata->dsps,
                rcdata->master);

        mem_error_if(new_dest == NULL, rcdata->graph, NULL, sr);
        mem_error_if(
                !AAtree_ins(rcdata->graph->nodes, new_dest),
                rcdata->graph,
                new_dest,
                sr);
    }
    Device_node* dest_node = AAtree_get_exact(rcdata->graph->nodes, dest_name);

    assert(src_node != NULL);
    assert(dest_node != NULL);
    mem_error_if(
            !Device_node_connect(dest_node, dest_port, src_node, src_port),
            rcdata->graph,
            NULL,
            sr);

    return true;
}

Connections* new_Connections_from_string(
        Streader* sr,
        Connection_level level,
        Ins_table* insts,
        Effect_table* effects,
        const DSP_table* dsps,
        Device* master)
{
    assert(sr != NULL);
    assert((level & ~(CONNECTION_LEVEL_INSTRUMENT |
                     CONNECTION_LEVEL_EFFECT)) == 0);
    assert(insts != NULL);
    assert(effects != NULL);
    assert(!(level & CONNECTION_LEVEL_EFFECT) || (dsps != NULL));
    assert((dsps == NULL) || (level & CONNECTION_LEVEL_EFFECT));
    assert(master != NULL);

    if (Streader_is_error_set(sr))
        return NULL;

    Connections* graph = memory_alloc_item(Connections);
    if (graph == NULL)
    {
        Streader_set_memory_error(
                sr, "Could not allocate memory for connections");
        return NULL;
    }

    graph->nodes = NULL;
    graph->iter = NULL;
    graph->nodes = new_AAtree(
            (int (*)(const void*, const void*))Device_node_cmp,
            (void (*)(void*))del_Device_node);
    mem_error_if(graph->nodes == NULL, graph, NULL, sr);
    graph->iter = new_AAiter(graph->nodes);
    mem_error_if(graph->iter == NULL, graph, NULL, sr);

    Device_node* master_node = NULL;
    if ((level & CONNECTION_LEVEL_EFFECT))
    {
        const Device* iface = Effect_get_output_interface((Effect*)master);
        master_node = new_Device_node("", insts, effects, dsps, iface);
    }
    else
    {
        master_node = new_Device_node("", insts, effects, dsps, master);
    }
    mem_error_if(master_node == NULL, graph, NULL, sr);
    mem_error_if(!AAtree_ins(graph->nodes, master_node), graph, master_node, sr);

    if (!Streader_has_data(sr))
    {
        Connections_reset(graph);
        return graph;
    }

    read_conn_data rcdata = { graph, level, insts, effects, dsps, master };
    if (!Streader_read_list(sr, read_connection, &rcdata))
    {
        del_Connections(graph);
        return NULL;
    }

    if (Connections_is_cyclic(graph))
    {
        Streader_set_error(sr, "The connection graph contains a cycle");
        del_Connections(graph);
        return NULL;
    }

    Connections_reset(graph);

    return graph;
}

#undef mem_error_if


Device_node* Connections_get_master(Connections* graph)
{
    assert(graph != NULL);
    return AAtree_get_exact(graph->nodes, "");
}


bool Connections_prepare(Connections* graph, Device_states* states)
{
    assert(graph != NULL);
    assert(states != NULL);

    return Connections_init_buffers(graph, states);
}


bool Connections_init_buffers(Connections* graph, Device_states* states)
{
    assert(graph != NULL);
    assert(states != NULL);

    Device_node* master = AAtree_get_exact(graph->nodes, "");
    assert(master != NULL);
    Device_node_reset(master);
    if (!Device_node_init_buffers_simple(master, states))
        return false;

    Device_node_reset(master);
    return Device_node_init_effect_buffers(master, states);
}


void Connections_clear_buffers(
        Connections* graph,
        Device_states* states,
        uint32_t start,
        uint32_t until)
{
    assert(graph != NULL);
    assert(states != NULL);

    Device_node* master = AAtree_get_exact(graph->nodes, "");
    assert(master != NULL);
    if (start >= until)
        return;

    Device_node_reset(master);
    Device_node_clear_buffers(master, states, start, until);

    return;
}


void Connections_mix(
        Connections* graph,
        Device_states* states,
        uint32_t start,
        uint32_t until,
        uint32_t freq,
        double tempo)
{
    assert(graph != NULL);
    assert(states != NULL);
    assert(freq > 0);
    assert(isfinite(tempo));
    assert(tempo > 0);

    Device_node* master = AAtree_get_exact(graph->nodes, "");
    assert(master != NULL);
    if (start >= until)
        return;

#if 0
    static bool called = false;
    if (!called)
    {
        Connections_print(graph, stderr);
    }
    called = true;
//    fprintf(stderr, "Mix process:\n");
#endif

    Device_node_reset(master);
    Device_node_mix(master, states, start, until, freq, tempo);

    return;
}


static void Connections_reset(Connections* graph)
{
    assert(graph != NULL);

    const char* name = "";
    Device_node* node = AAiter_get_at_least(graph->iter, name);
    while (node != NULL)
    {
        Device_node_set_state(node, DEVICE_NODE_STATE_NEW);
        node = AAiter_get_next(graph->iter);
    }

    return;
}


static bool Connections_is_cyclic(Connections* graph)
{
    assert(graph != NULL);

    Connections_reset(graph);
    const char* name = "";
    Device_node* node = AAiter_get_at_least(graph->iter, name);
    while (node != NULL)
    {
        assert(Device_node_get_state(node) != DEVICE_NODE_STATE_REACHED);
        if (Device_node_cycle_in_path(node))
            return true;

        node = AAiter_get_next(graph->iter);
    }
    return false;
}


void Connections_print(Connections* graph, FILE* out)
{
    assert(graph != NULL);
    assert(out != NULL);

//    Connections_reset(graph);
    Device_node* master = AAtree_get_exact(graph->nodes, "");
    assert(master != NULL);
    Device_node_print(master, out);
    fprintf(out, "\n");

    return;
}


void del_Connections(Connections* graph)
{
    if (graph == NULL)
        return;

    del_AAiter(graph->iter);
    del_AAtree(graph->nodes);
    memory_free(graph);

    return;
}


static int read_index(char* str)
{
    assert(str != NULL);

    static const char* hex_digits = "0123456789abcdef";
    if (strspn(str, hex_digits) != 2)
        return INT_MAX;

    int res = (strchr(hex_digits, str[0]) - hex_digits) * 0x10;

    return res + (strchr(hex_digits, str[1]) - hex_digits);
}


static int validate_connection_path(
        Streader* sr,
        char* str,
        Connection_level level,
        Device_port_type type)
{
    assert(sr != NULL);
    assert(str != NULL);
    assert(type < DEVICE_PORT_TYPES);

    if (Streader_is_error_set(sr))
        return -1;

    bool instrument = false;
    bool generator = false;
    //bool effect = false;
    //bool dsp = false;
    bool root = true;
    char* path = str;
    char* trim_point = str;

    if (string_has_prefix(str, "ins_"))
    {
        if (level != CONNECTION_LEVEL_GLOBAL)
        {
            Streader_set_error(
                    sr,
                    "Instrument directory in a deep-level connection: \"%s\"",
                    path);
            return -1;
        }

        instrument = true;
        root = false;
        str += strlen("ins_");
        if (read_index(str) >= KQT_INSTRUMENTS_MAX)
        {
            Streader_set_error(
                    sr,
                    "Invalid instrument number in the connection: \"%s\"",
                    path);
            return -1;
        }

        str += 2;
        if (!string_has_prefix(str, "/"))
        {
            Streader_set_error(
                    sr,
                    "Missing trailing '/' after the instrument number"
                        " in the connection: \"%s\"",
                    path);
            return -1;
        }

        ++str;
        trim_point = str - 1;
    }
    else if (string_has_prefix(str, "eff_"))
    {
        if ((level & CONNECTION_LEVEL_EFFECT))
        {
            Streader_set_error(
                    sr,
                    "Effect directory in an effect-level connection: \"%s\"",
                    path);
            return -1;
        }

        //effect = true;
        root = false;
        str += strlen("eff_");
        int max = KQT_EFFECTS_MAX;
        if ((level & CONNECTION_LEVEL_INSTRUMENT))
            max = KQT_INST_EFFECTS_MAX;

        if (read_index(str) >= max)
        {
            Streader_set_error(
                    sr,
                    "Invalid effect number in the connection: \"%s\"",
                    path);
            return -1;
        }

        str += 2;
        if (!string_has_prefix(str, "/"))
        {
            Streader_set_error(
                    sr,
                    "Missing trailing '/' after the effect number in"
                        " the connection: \"%s\"",
                    path);
            return -1;
        }

        ++str;
        trim_point = str - 1;
    }
    else if (string_has_prefix(str, "gen_"))
    {
        if (!(level & CONNECTION_LEVEL_INSTRUMENT))
        {
            Streader_set_error(
                    sr,
                    "Generator directory in a root-level connection: \"%s\"",
                    path);
            return -1;
        }
        if ((level & CONNECTION_LEVEL_EFFECT))
        {
            Streader_set_error(
                    sr,
                    "Generator directory in an effect-level connection: \"%s\"",
                    path);
            return -1;
        }

        root = false;
        generator = true;
        str += strlen("gen_");
        if (read_index(str) >= KQT_GENERATORS_MAX)
        {
            Streader_set_error(
                    sr,
                    "Invalid generator number in the connection: \"%s\"",
                    path);
            return -1;
        }

        str += 2;
        if (!string_has_prefix(str, "/"))
        {
            Streader_set_error(
                    sr,
                    "Missing trailing '/' after the generator number"
                        " in the connection: \"%s\"",
                    path);
            return -1;
        }

        ++str;
        if (!string_has_prefix(str, "C/"))
        {
            Streader_set_error(
                    sr,
                    "Invalid generator parameter directory"
                        " in the connection: \"%s\"",
                    path);
            return -1;
        }

        str += strlen("C/");
        trim_point = str - 1;
    }
    else if (string_has_prefix(str, "dsp_"))
    {
        if (!(level & CONNECTION_LEVEL_EFFECT))
        {
            Streader_set_error(
                    sr, "DSP directory outside an effect: \"%s\"", path);
            return -1;
        }

        root = false;
        //dsp = true;
        str += strlen("dsp_");
        if (read_index(str) >= KQT_DSPS_MAX)
        {
            Streader_set_error(
                    sr, "Invalid DSP number in the connection: \"%s\"", path);
            return -1;
        }

        str += 2;
        if (!string_has_prefix(str, "/"))
        {
            Streader_set_error(
                    sr,
                    "Missing trailing '/' after the DSP number"
                        " in the connection: \"%s\"",
                    path);
            return -1;
        }

        ++str;
        if (!string_has_prefix(str, "C/"))
        {
            Streader_set_error(
                    sr,
                    "Invalid DSP parameter directory"
                        " in the connection: \"%s\"",
                    path);
            return -1;
        }

        str += strlen("C/");
        trim_point = str - 1;
    }
    if (string_has_prefix(str, "in_") || string_has_prefix(str, "out_"))
    {
        // TODO: check effect connections
        if (string_has_prefix(str, "in_") && (instrument || generator))
        {
            Streader_set_error(
                    sr,
                    "Input ports are not allowed for instruments"
                        " or generators: \"%s\"",
                    path);
            return -1;
        }

        if (string_has_prefix(str, "in_") && root &&
                !(level & CONNECTION_LEVEL_EFFECT))
        {
            Streader_set_error(
                    sr, "Input ports are not allowed for master: \"%s\"", path);
            return -1;
        }

        if (type == DEVICE_PORT_TYPE_RECEIVE)
        {
            bool can_receive = (!root && string_has_prefix(str, "in_")) ||
                               (root && string_has_prefix(str, "out_"));
            if (!can_receive)
            {
                Streader_set_error(
                        sr,
                        "Destination port is not for receiving data: \"%s\"",
                        path);
                return -1;
            }
        }
        else
        {
            assert(type == DEVICE_PORT_TYPE_SEND);
            bool can_send = (string_has_prefix(str, "out_") && !root) ||
                            (string_has_prefix(str, "in_") && root);
            if (!can_send)
            {
                Streader_set_error(
                        sr,
                        "Source port is not for sending data: \"%s\"",
                        path);
                return -1;
            }
        }

        str += strcspn(str, "_") + 1;
        int port = read_index(str);
        if (port >= KQT_DEVICE_PORTS_MAX)
        {
            Streader_set_error(sr, "Invalid port number: \"%s\"", path);
            return -1;
        }

        str += 2;
        if (str[0] != '/' && str[0] != '\0' && str[1] != '\0')
        {
            Streader_set_error(
                    sr,
                    "Connection path contains garbage"
                        " after the port specification: \"%s\"",
                    path);
            return -1;
        }

        *trim_point = '\0';
        return port;
    }

    Streader_set_error(sr, "Invalid connection: \"%s\"", path);

    return -1;
}


