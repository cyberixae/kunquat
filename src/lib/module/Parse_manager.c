

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
#include <string.h>
#include <ctype.h>
#include <inttypes.h>

#include <Connections.h>
#include <debug/assert.h>
#include <devices/Device_event_keys.h>
#include <devices/Device_params.h>
#include <devices/dsps/DSP_type.h>
#include <devices/generators/Gen_type.h>
#include <Handle_private.h>
#include <memory.h>
#include <module/Bind.h>
#include <module/Environment.h>
#include <module/manifest.h>
#include <module/Parse_manager.h>
#include <string/Streader.h>
#include <string/common.h>


static bool parse_module_level(
        Handle* handle,
        const char* key,
        Streader* sr);


static bool parse_album_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr);


static bool parse_instrument_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr,
        int index);


static bool parse_effect_level(
        Handle* handle,
        Instrument* ins,
        const char* key,
        const char* subkey,
        Streader* sr,
        int eff_index);


static bool parse_generator_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr,
        int ins_index,
        int gen_index);


static bool parse_dsp_level(
        Handle* handle,
        Effect* eff,
        const char* key,
        const char* subkey,
        Streader* sr,
        int dsp_index);


static bool parse_pattern_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr,
        int index);


static bool parse_pat_inst_level(
        Handle* handle,
        Pattern* pat,
        const char* key,
        const char* subkey,
        Streader* sr,
        int index);


static bool parse_scale_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr,
        int index);


static bool parse_subsong_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr,
        int index);


#define set_error(handle, sr)                                               \
    if (true)                                                               \
    {                                                                       \
        if (Error_get_type(&(sr)->error) == ERROR_FORMAT)                   \
            Handle_set_validation_error_from_Error((handle), &(sr)->error); \
        else                                                                \
            Handle_set_error_from_Error((handle), &(sr)->error);            \
    } else (void)0


static bool prepare_connections(Handle* handle)
{
    assert(handle != NULL);

    Module* module = Handle_get_module(handle);
    Connections* graph = module->connections;

    Device_states* states = Player_get_device_states(handle->player);

    if (!Connections_prepare(graph, states))
    {
        Handle_set_error(handle, ERROR_MEMORY,
                "Couldn't allocate memory for connections");
        return false;
    }

    return true;
}


bool parse_data(
        Handle* handle,
        const char* key,
        const void* data,
        long length)
{
//    fprintf(stderr, "parsing %s\n", key);
    assert(handle != NULL);
    check_key(handle, key, false);
    assert(data != NULL || length == 0);
    assert(length >= 0);

    if (length == 0)
    {
        data = NULL;
    }

    int last_index = 0;
    const char* last_element = strrchr(key, '/');
    if (last_element == NULL)
    {
        last_element = key;
    }
    else
    {
        ++last_element;
        last_index = last_element - key;
    }
    if (strncmp(last_element, "p_", 2) != 0)
    {
        return true;
    }

    Streader* sr = Streader_init(STREADER_AUTO, data, length);

    if (last_index == 0)
    {
        bool success = parse_module_level(handle, key, sr);
        return success;
    }

    Module* module = Handle_get_module(handle);

    int first_len = strcspn(key, "/");
    int index = 0;
    const char* second_element = &key[first_len + 1];
    bool success = true;
    if ((index = string_extract_index(key, "ins_", 2, "/")) >= 0)
    {
        Instrument* ins = Ins_table_get(Module_get_insts(module), index);
        bool changed = ins != NULL;
        success = parse_instrument_level(handle, key, second_element,
                                         sr, index);
        changed ^= Ins_table_get(Module_get_insts(module), index) != NULL;
        Connections* graph = module->connections;
        if (changed && graph != NULL)
        {
            if (!prepare_connections(handle))
                return false;
            //fprintf(stderr, "line: %d\n", __LINE__);
            //Connections_print(graph, stderr);
        }
    }
    else if ((index = string_extract_index(key, "control_", 2, "/")) >= 0)
    {
        if (index < 0 || index >= KQT_CONTROLS_MAX)
            return true;

        if (string_eq(second_element, "p_manifest.json"))
        {
            const bool existent = read_default_manifest(sr);
            if (Streader_is_error_set(sr))
            {
                set_error(handle, sr);
                return false;
            }
            Module_set_control(handle->module, index, existent);
        }
    }
    else if ((index = string_extract_index(key, "eff_", 2, "/")) >= 0)
    {
        const Effect* eff = Effect_table_get(Module_get_effects(module), index);
        bool changed = eff != NULL;
        success = parse_effect_level(handle, NULL, key, second_element,
                                     sr, index);
        changed ^= Effect_table_get(Module_get_effects(module), index) != NULL;
        Connections* graph = module->connections;
        if (changed && graph != NULL)
        {
            if (!prepare_connections(handle))
                return false;
        }
    }
    else if ((index = string_extract_index(key, "pat_", 3, "/")) >= 0)
    {
        Pattern* pat = Pat_table_get(Module_get_pats(module), index);
        success = parse_pattern_level(handle, key, second_element,
                                      sr, index);
        Pattern* new_pat = Pat_table_get(Module_get_pats(module), index);
        if (success && pat != new_pat && new_pat != NULL)
        {
            // Update pattern location information
            // This is needed for correct jump counter updates
            // when a Pattern with jumps is used multiple times.
#if 0
            for (int subsong = 0; subsong < KQT_SONGS_MAX; ++subsong)
            {
                const Order_list* ol = module->order_lists[subsong];
                if (ol == NULL)
                    continue;

                const size_t ol_len = Order_list_get_len(ol);
                for (size_t system = 0; system < ol_len; ++system)
                {
                    Pat_inst_ref* ref = Order_list_get_pat_inst_ref(ol, system);
                    if (ref->pat == index)
                    {
                        if (!Pattern_set_location(new_pat, subsong, ref))
                        {
                            Handle_set_error(handle, ERROR_MEMORY,
                                    "Couldn't allocate memory");
                            return false;
                        }
                    }
                }
#if 0
                Subsong* ss = Subsong_table_get_hidden(
                                      Module_get_subsongs(module),
                                      subsong);
                if (ss == NULL)
                {
                    continue;
                }
                for (int section = 0; section < KQT_SECTIONS_MAX; ++section)
                {
                    if (Subsong_get(ss, section) == index)
                    {
                        if (!Pattern_set_location(new_pat, subsong, section))
                        {
                            Handle_set_error(handle, ERROR_MEMORY,
                                    "Couldn't allocate memory");
                            return false;
                        }
                    }
                }
#endif
            }
#endif
        }
    }
    else if ((index = string_extract_index(key, "scale_", 1, "/")) >= 0)
    {
        success = parse_scale_level(handle, key, second_element,
                                    sr, index);
    }
    else if ((index = string_extract_index(key, "song_", 2, "/")) >= 0)
    {
        success = parse_subsong_level(handle, key, second_element,
                                      sr, index);
    }
    else if (string_has_prefix(key, "album/"))
    {
        success = parse_album_level(handle, key, second_element, sr);
    }

    return success;
}


static bool parse_module_level(
        Handle* handle,
        const char* key,
        Streader* sr)
{
//    fprintf(stderr, "song level: %s\n", key);
    assert(handle != NULL);
    assert(key != NULL);
    assert(sr != NULL);

    Module* module = Handle_get_module(handle);

    if (string_eq(key, "p_composition.json"))
    {
        if (!Module_parse_composition(module, sr))
        {
            set_error(handle, sr);
            return false;
        }
    }
    else if (string_eq(key, "p_connections.json"))
    {
        Connections* graph = new_Connections_from_string(sr,
                                            CONNECTION_LEVEL_GLOBAL,
                                            Module_get_insts(module),
                                            Module_get_effects(module),
                                            NULL,
                                            (Device*)module);
        if (graph == NULL)
        {
            set_error(handle, sr);
            return false;
        }
        if (module->connections != NULL)
        {
            del_Connections(module->connections);
        }
        module->connections = graph;
        //fprintf(stderr, "line: %d\n", __LINE__);
        //Connections_print(graph, stderr);
        if (!prepare_connections(handle))
            return false;
        //fprintf(stderr, "line: %d\n", __LINE__);
        //Connections_print(graph, stderr);
    }
    else if (string_eq(key, "p_control_map.json"))
    {
        if (!Module_set_ins_map(module, sr))
        {
            set_error(handle, sr);
            return false;
        }
    }
    else if (string_eq(key, "p_random_seed.json"))
    {
        if (!Module_parse_random_seed(module, sr))
        {
            set_error(handle, sr);
            return false;
        }
    }
    else if (string_eq(key, "p_environment.json"))
    {
        if (!Environment_parse(module->env, sr))
        {
            set_error(handle, sr);
            return false;
        }
        if (!Player_refresh_env_state(handle->player))
        {
            Handle_set_error(handle, ERROR_MEMORY,
                    "Couldn't allocate memory for environment state");
            return false;
        }
    }
    else if (string_eq(key, "p_bind.json"))
    {
        Bind* map = new_Bind(
                sr,
                Event_handler_get_names(
                    Player_get_event_handler(handle->player)));
        if (map == NULL)
        {
            set_error(handle, sr);
            return false;
        }
        Module_set_bind(module, map);

        if (!Player_refresh_bind_state(handle->player))
        {
            Handle_set_error(handle, ERROR_MEMORY,
                    "Couldn't allocate memory for bind state");
            return false;
        }
    }
    return true;
}


static bool parse_album_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr)
{
    assert(handle != NULL);
    assert(key != NULL);
    assert(subkey != NULL);
    assert(sr != NULL);
    (void)key;

    Module* module = Handle_get_module(handle);

    if (string_eq(subkey, "p_manifest.json"))
    {
        const bool existent = read_default_manifest(sr);
        if (Streader_is_error_set(sr))
        {
            set_error(handle, sr);
            return false;
        }
        module->album_is_existent = existent;
    }
    else if (string_eq(subkey, "p_tracks.json"))
    {
        Track_list* tl = new_Track_list(sr);
        if (tl == NULL)
        {
            set_error(handle, sr);
            return false;
        }
        del_Track_list(module->track_list);
        module->track_list = tl;
    }
    return true;
}


static Instrument* add_instrument(Handle* handle, int index)
{
    assert(handle != NULL);
    assert(index >= 0);
    assert(index < KQT_INSTRUMENTS_MAX);

    static const char* memory_error_str =
        "Couldn't allocate memory for a new instrument";

    Module* module = Handle_get_module(handle);

    // Return existing instrument
    Instrument* ins = Ins_table_get(Module_get_insts(module), index);
    if (ins != NULL)
        return ins;

    // Create new instrument
    ins = new_Instrument();
    if (ins == NULL || !Ins_table_set(Module_get_insts(module), index, ins))
    {
        Handle_set_error(handle, ERROR_MEMORY, memory_error_str);
        del_Instrument(ins);
        return NULL;
    }

    // Allocate Device state(s) for the new Instrument
    Device_state* ds = Device_create_state(
            (Device*)ins,
            Player_get_audio_rate(handle->player),
            Player_get_audio_buffer_size(handle->player));
    if (ds == NULL || !Device_states_add_state(
                Player_get_device_states(handle->player), ds))
    {
        Handle_set_error(handle, ERROR_MEMORY, memory_error_str);
        Ins_table_remove(Module_get_insts(module), index);
        return NULL;
    }

    return ins;
}


static bool parse_instrument_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr,
        int index)
{
//    fprintf(stderr, "instrument level: %s\n", key);
    assert(handle != NULL);
    assert(key != NULL);
    assert(subkey != NULL);
    assert(sr != NULL);

    if (index < 0 || index >= KQT_INSTRUMENTS_MAX)
        return true;

#if 0
    if (!string_has_prefix(subkey, MAGIC_ID "iXX/") &&
            !string_has_prefix(subkey, MAGIC_ID "i" KQT_FORMAT_VERSION "/"))
    {
        return true;
    }
    subkey = strchr(subkey, '/');
    assert(subkey != NULL);
    ++subkey;
#endif
    int gen_index = -1;
    int eff_index = -1;

    Module* module = Handle_get_module(handle);

    // Subdevices
    if ((gen_index = string_extract_index(subkey, "gen_", 2, "/")) >= 0)
    {
        subkey = strchr(subkey, '/');
        assert(subkey != NULL);
        ++subkey;
        Instrument* ins = Ins_table_get(Module_get_insts(module), index);
        const Generator* gen = (ins != NULL)
            ? Instrument_get_gen(ins, gen_index) : NULL;
        bool changed = (ins != NULL) && (gen != NULL) &&
            Device_has_complete_type((const Device*)gen);
        bool success = parse_generator_level(handle, key, subkey,
                                             sr,
                                             index, gen_index);
        ins = Ins_table_get(Module_get_insts(module), index);
        gen = ins != NULL ? Instrument_get_gen(ins, gen_index) : NULL;
        changed ^= ins != NULL && gen != NULL &&
            Device_has_complete_type((const Device*)gen);
        Connections* graph = module->connections;
        if (changed && graph != NULL)
        {
            if (!prepare_connections(handle))
                return false;
            //fprintf(stderr, "line: %d\n", __LINE__);
            //Connections_print(graph, stderr);
        }
        return success;
    }
    else if ((eff_index = string_extract_index(subkey, "eff_", 2, "/")) >= 0)
    {
        subkey = strchr(subkey, '/');
        assert(subkey != NULL);
        ++subkey;
        Instrument* ins = Ins_table_get(Module_get_insts(module), index);
        bool changed = ins != NULL && Instrument_get_effect(ins,
                                                eff_index) != NULL;

        ins = add_instrument(handle, index);
        if (ins == NULL)
            return false;

        bool success = parse_effect_level(handle, ins, key, subkey,
                                          sr, eff_index);
        changed ^= ins != NULL &&
                   Instrument_get_effect(ins, eff_index) != NULL;
        Connections* graph = module->connections;
        if (changed && graph != NULL)
        {
            if (!prepare_connections(handle))
                return false;
        }
        return success;
    }

    // Instrument data
    if (string_eq(subkey, "p_manifest.json"))
    {
        Instrument* ins = Ins_table_get(Module_get_insts(module), index);
        ins = add_instrument(handle, index);
        if (ins == NULL)
            return false;

        const bool existent = read_default_manifest(sr);
        if (Streader_is_error_set(sr))
        {
            set_error(handle, sr);
            return false;
        }

        Device_set_existent((Device*)ins, existent);
    }
    else if (string_eq(subkey, "p_instrument.json"))
    {
        Instrument* ins = Ins_table_get(Module_get_insts(module), index);
        ins = add_instrument(handle, index);
        if (ins == NULL)
            return false;

        if (!Instrument_parse_header(ins, sr))
        {
            set_error(handle, sr);
            return false;
        }
    }
    else if (string_eq(subkey, "p_connections.json"))
    {
        bool reconnect = false;
        Instrument* ins = Ins_table_get(Module_get_insts(module), index);
        if (!Streader_has_data(sr))
        {
            if (ins != NULL)
            {
                Instrument_set_connections(ins, NULL);
                reconnect = true;
            }
        }
        else
        {
            ins = add_instrument(handle, index);
            if (ins == NULL)
                return false;

            Connections* graph = new_Connections_from_string(sr,
                                                 CONNECTION_LEVEL_INSTRUMENT,
                                                 Module_get_insts(module),
                                                 Instrument_get_effects(ins),
                                                 NULL,
                                                 (Device*)ins);
            if (graph == NULL)
            {
                set_error(handle, sr);
                return false;
            }
            Instrument_set_connections(ins, graph);
            reconnect = true;
        }
        if (reconnect)
        {
//            fprintf(stderr, "Set connections for ins %d\n", index);
            Connections* global_graph = module->connections;
            if (global_graph != NULL)
            {
                if (!prepare_connections(handle))
                    return false;
//                fprintf(stderr, "line: %d\n", __LINE__);
//                Connections_print(global_graph, stderr);
            }
        }
    }
    else if (string_has_prefix(subkey, "p_pitch_lock_"))
    {
        Instrument* ins = Ins_table_get(Module_get_insts(module), index);
        ins = add_instrument(handle, index);
        if (ins == NULL)
            return false;

        if (!Instrument_parse_value(ins, subkey, sr))
        {
            set_error(handle, sr);
            return false;
        }
    }

    static const struct
    {
        const char* name;
        bool (*read)(Instrument_params*, Streader*);
    } parse[] =
    {
        { "p_envelope_force.json", Instrument_params_parse_env_force },
        { "p_envelope_force_release.json", Instrument_params_parse_env_force_rel },
        { "p_envelope_force_filter.json", Instrument_params_parse_env_force_filter },
        { "p_envelope_pitch_pan.json", Instrument_params_parse_env_pitch_pan },
        { NULL, NULL }
    };

    for (int i = 0; parse[i].name != NULL; ++i)
    {
        assert(parse[i].read != NULL);
        if (string_eq(subkey, parse[i].name))
        {
            Instrument* ins = Ins_table_get(Module_get_insts(module), index);
            ins = add_instrument(handle, index);
            if (ins == NULL)
                return false;

            if (!parse[i].read(Instrument_get_params(ins), sr))
            {
                set_error(handle, sr);
                return false;
            }
        }
    }
    return true;
}


static Generator* add_generator(
        Handle* handle,
        Instrument* ins,
        Gen_table* gen_table,
        int gen_index)
{
    assert(handle != NULL);
    assert(ins != NULL);
    assert(gen_table != NULL);
    assert(gen_index >= 0);
    assert(gen_index < KQT_GENERATORS_MAX);

    static const char* memory_error_str =
        "Couldn't allocate memory for a new generator";

    // Return existing generator
    Generator* gen = Gen_table_get_gen_mut(gen_table, gen_index);
    if (gen != NULL)
        return gen;

    // Create new generator
    gen = new_Generator(Instrument_get_params(ins));
    if (gen == NULL || !Gen_table_set_gen(gen_table, gen_index, gen))
    {
        Handle_set_error(handle, ERROR_MEMORY, memory_error_str);
        del_Generator(gen);
        return NULL;
    }

    return gen;
}


static bool parse_generator_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr,
        int ins_index,
        int gen_index)
{
//    fprintf(stderr, "generator level: %s\n", key);
    assert(handle != NULL);
    assert(key != NULL);
    assert(subkey != NULL);
    assert(sr != NULL);
    assert(ins_index >= 0);
    assert(ins_index < KQT_INSTRUMENTS_MAX);
    (void)key;

    if (gen_index < 0 || gen_index >= KQT_GENERATORS_MAX)
        return true;

#if 0
    if (!string_has_prefix(subkey, MAGIC_ID "gXX/") &&
            !string_has_prefix(subkey, MAGIC_ID "g" KQT_FORMAT_VERSION "/"))
        return true;

    subkey = strchr(subkey, '/');
    ++subkey;
#endif

    Module* module = Handle_get_module(handle);

    Instrument* ins = Ins_table_get(Module_get_insts(module), ins_index);
    ins = add_instrument(handle, ins_index);
    if (ins == NULL)
        return false;

    Gen_table* table = Instrument_get_gens(ins);
    assert(table != NULL);

    if (string_eq(subkey, "p_manifest.json"))
    {
        const bool existent = read_default_manifest(sr);
        if (Streader_is_error_set(sr))
        {
            set_error(handle, sr);
            return false;
        }

        Gen_table_set_existent(table, gen_index, existent);
    }
    else if (string_eq(subkey, "p_gen_type.json"))
    {
        if (!Streader_has_data(sr))
        {
            const Generator* gen = Gen_table_get_gen(table, gen_index);
            if (gen != NULL)
            {
                //Connections_disconnect(module->connections,
                //                       (Device*)gen);
            }
            Gen_table_remove_gen(table, gen_index);
        }
        else
        {
            Generator* gen = add_generator(handle, ins, table, gen_index);
            if (gen == NULL)
                return false;

            // Create the Generator implementation
            char type[GEN_TYPE_LENGTH_MAX] = "";
            if (!Streader_read_string(sr, GEN_TYPE_LENGTH_MAX, type))
            {
                set_error(handle, sr);
                return false;
            }
            Generator_cons* cons = Gen_type_find_cons(type);
            if (cons == NULL)
            {
                Handle_set_error(handle, ERROR_FORMAT,
                        "Unsupported Generator type: %s", type);
                return false;
            }
            Device_impl* gen_impl = cons(gen);
            if (gen_impl == NULL)
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory for generator implementation");
                return false;
            }

            Device_set_impl((Device*)gen, gen_impl);

            // Remove old Generator Device state
            Device_states* dstates = Player_get_device_states(handle->player);
            Device_states_remove_state(dstates, Device_get_id((Device*)gen));

            // Get generator properties
            Generator_property* property = Gen_type_find_property(type);
            if (property != NULL)
            {
                // Allocate Voice state space
                const char* size_str = property(gen, "voice_state_size");
                if (size_str != NULL)
                {
                    Streader* size_sr = Streader_init(
                            STREADER_AUTO, size_str, strlen(size_str));
                    int64_t size = 0;
                    Streader_read_int(size_sr, &size);
                    assert(!Streader_is_error_set(sr));
                    assert(size >= 0);
//                    fprintf(stderr, "Reserving space for %" PRId64 " bytes\n",
//                                    size);
                    if (!Player_reserve_voice_state_space(
                                handle->player, size) ||
                            !Player_reserve_voice_state_space(
                                handle->length_counter, size))
                    {
                        Handle_set_error(handle, ERROR_MEMORY,
                                "Couldn't allocate memory");
                        del_Device_impl(gen_impl);
                        return false;
                    }
                }

                // Allocate channel-specific generator state space
                const char* gen_state_vars = property(gen, "gen_state_vars");
                if (gen_state_vars != NULL)
                {
                    Streader* gsv_sr = Streader_init(
                            STREADER_AUTO,
                            gen_state_vars,
                            strlen(gen_state_vars));

                    if (!Player_alloc_channel_gen_state_keys(
                                handle->player, gsv_sr))
                    {
                        set_error(handle, gsv_sr);
                        return false;
                    }
                }
            }

            // Allocate Device state(s) for this Generator
            Device_state* ds = Device_create_state(
                    (Device*)gen,
                    Player_get_audio_rate(handle->player),
                    Player_get_audio_buffer_size(handle->player));
            if (ds == NULL || !Device_states_add_state(dstates, ds))
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory");
                del_Device_state(ds);
                del_Generator(gen);
                return false;
            }

            // Sync the Generator
            if (!Device_sync((Device*)gen))
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory while syncing generator");
                return false;
            }

            // Sync the Device state(s)
            if (!Device_sync_states(
                        (Device*)gen,
                        Player_get_device_states(handle->player)))
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory while syncing generator");
                return false;
            }
        }
    }
#if 0
    else if (string_eq(subkey, "p_events.json"))
    {
        Generator* gen = add_generator(handle, ins, table, gen_index);
        if (gen == NULL)
            return false;

        Gen_conf* conf = add_gen_conf(handle, table, gen_index);
        if (conf == NULL)
            return false;

        Read_state* state = Read_state_init(READ_STATE_AUTO, key);
        if (!Device_params_parse_events(
                    conf->params,
                    DEVICE_EVENT_TYPE_GENERATOR,
                    handle->player,
                    data,
                    state))
        {
            set_parse_error(handle, state);
            return false;
        }
    }
#endif
    else if ((string_has_prefix(subkey, "i/") ||
              string_has_prefix(subkey, "c/")) &&
             key_is_device_param(subkey))
    {
        Generator* gen = add_generator(handle, ins, table, gen_index);
        if (gen == NULL)
            return false;

        // Update Device
        if (!Device_set_key((Device*)gen, subkey, sr))
        {
            set_error(handle, sr);
            return false;
        }

        // Update Device state
        Device_set_state_key(
                (Device*)gen,
                Player_get_device_states(handle->player),
                subkey);
    }

    return true;
}


static Effect* add_effect(Handle* handle, int index, Effect_table* table)
{
    assert(handle != NULL);
    assert(index >= 0);
    assert(table != NULL);

    static const char* memory_error_str =
        "Couldn't allocate memory for a new effect";

    // Return existing effect
    Effect* eff = Effect_table_get_mut(table, index);
    if (eff != NULL)
        return eff;

    // Create new effect
    eff = new_Effect();
    if (eff == NULL || !Effect_table_set(table, index, eff))
    {
        del_Effect(eff);
        Handle_set_error(handle, ERROR_MEMORY, memory_error_str);
        return NULL;
    }

    // Allocate Device states for the new Effect
    const Device* eff_devices[] =
    {
        (Device*)eff,
        Effect_get_input_interface(eff),
        Effect_get_output_interface(eff),
        NULL
    };
    for (int i = 0; i < 3; ++i)
    {
        assert(eff_devices[i] != NULL);
        Device_state* ds = Device_create_state(
                eff_devices[i],
                Player_get_audio_rate(handle->player),
                Player_get_audio_buffer_size(handle->player));
        if (ds == NULL || !Device_states_add_state(
                    Player_get_device_states(handle->player), ds))
        {
            del_Device_state(ds);
            Handle_set_error(handle, ERROR_MEMORY, memory_error_str);
            Effect_table_remove(table, index);
            return NULL;
        }
    }

    return eff;
}


static bool parse_effect_level(
        Handle* handle,
        Instrument* ins,
        const char* key,
        const char* subkey,
        Streader* sr,
        int eff_index)
{
    assert(handle != NULL);
    assert(key != NULL);
    assert(subkey != NULL);
    assert(sr != NULL);

    int max_index = KQT_EFFECTS_MAX;
    if (ins != NULL)
        max_index = KQT_INST_EFFECTS_MAX;

    if (eff_index < 0 || eff_index >= max_index)
        return true;

#if 0
    if (!string_has_prefix(subkey, MAGIC_ID "eXX/") &&
            !string_has_prefix(subkey, MAGIC_ID "e" KQT_FORMAT_VERSION "/"))
    {
        return true;
    }
    subkey = strchr(subkey, '/') + 1;
#endif

    Module* module = Handle_get_module(handle);

    int dsp_index = -1;
    Effect_table* table = Module_get_effects(module);
    if (ins != NULL)
        table = Instrument_get_effects(ins);

    if ((dsp_index = string_extract_index(subkey, "dsp_", 2, "/")) >= 0)
    {
        subkey = strchr(subkey, '/');
        assert(subkey != NULL);
        ++subkey;
        Effect* eff = Effect_table_get_mut(table, eff_index);
        bool changed = (eff != NULL) && (Effect_get_dsp(eff, dsp_index) != NULL) &&
            Device_has_complete_type((const Device*)Effect_get_dsp(eff, dsp_index));

        eff = add_effect(handle, eff_index, table);
        if (eff == NULL)
            return false;

        bool success = parse_dsp_level(handle, eff, key, subkey, sr, dsp_index);
        changed ^= (eff != NULL) && (Effect_get_dsp(eff, dsp_index) != NULL) &&
            Device_has_complete_type((const Device*)Effect_get_dsp(eff, dsp_index));
        Connections* graph = module->connections;
        if (changed && graph != NULL)
        {
            if (!prepare_connections(handle))
                return false;
        }
        return success;
    }
    else if (string_eq(subkey, "p_manifest.json"))
    {
        Effect* eff = add_effect(handle, eff_index, table);
        if (eff == NULL)
            return false;

        const bool existent = read_default_manifest(sr);
        if (Streader_is_error_set(sr))
        {
            set_error(handle, sr);
            return false;
        }
        Device_set_existent((Device*)eff, existent);
    }
    else if (string_eq(subkey, "p_connections.json"))
    {
        bool reconnect = false;
        Effect* eff = Effect_table_get_mut(table, eff_index);
        if (!Streader_has_data(sr))
        {
            if (eff != NULL)
            {
                Effect_set_connections(eff, NULL);
                reconnect = true;
            }
        }
        else
        {
            eff = add_effect(handle, eff_index, table);
            if (eff == NULL)
                return false;

            Connection_level level = CONNECTION_LEVEL_EFFECT;
            if (ins != NULL)
            {
                level |= CONNECTION_LEVEL_INSTRUMENT;
            }
            Connections* graph = new_Connections_from_string(
                    sr,
                    level,
                    Module_get_insts(module),
                    table,
                    Effect_get_dsps(eff),
                    (Device*)eff);
            if (graph == NULL)
            {
                set_error(handle, sr);
                return false;
            }
            Effect_set_connections(eff, graph);
            reconnect = true;
        }
        if (reconnect)
        {
            Connections* global_graph = module->connections;
            if (global_graph != NULL)
            {
                if (!prepare_connections(handle))
                    return false;
            }
        }
    }

    return true;
}


static DSP* add_dsp(
        Handle* handle,
        DSP_table* dsp_table,
        int dsp_index)
{
    assert(handle != NULL);
    assert(dsp_table != NULL);
    assert(dsp_index >= 0);
    //assert(dsp_index < KQT_DSPS_MAX);

    static const char* memory_error_str =
        "Couldn't allocate memory for a new DSP";

    // Return existing DSP
    DSP* dsp = DSP_table_get_dsp(dsp_table, dsp_index);
    if (dsp != NULL)
        return dsp;

    // Create new DSP
    dsp = new_DSP();
    if (dsp == NULL || !DSP_table_set_dsp(dsp_table, dsp_index, dsp))
    {
        Handle_set_error(handle, ERROR_MEMORY, memory_error_str);
        del_DSP(dsp);
        return NULL;
    }

    return dsp;
}


static bool parse_dsp_level(
        Handle* handle,
        Effect* eff,
        const char* key,
        const char* subkey,
        Streader* sr,
        int dsp_index)
{
    assert(handle != NULL);
    assert(eff != NULL);
    assert(key != NULL);
    assert(subkey != NULL);
    assert(sr != NULL);
    (void)key;

    if (dsp_index < 0 || dsp_index >= KQT_DSPS_MAX)
        return true;

#if 0
    if (!string_has_prefix(subkey, MAGIC_ID "dXX/") &&
            !string_has_prefix(subkey, MAGIC_ID "d" KQT_FORMAT_VERSION "/"))
        return true;

    subkey = strchr(subkey, '/') + 1;
#endif

    DSP_table* dsp_table = Effect_get_dsps_mut(eff);
    assert(dsp_table != NULL);

    if (string_eq(subkey, "p_manifest.json"))
    {
        const bool existent = read_default_manifest(sr);
        if (Streader_is_error_set(sr))
        {
            set_error(handle, sr);
            return false;
        }

        DSP_table_set_existent(dsp_table, dsp_index, existent);
    }
    else if (string_eq(subkey, "p_dsp_type.json"))
    {
//        fprintf(stderr, "%s\n", subkey);
        if (!Streader_has_data(sr))
        {
            DSP_table_remove_dsp(dsp_table, dsp_index);
        }
        else
        {
            DSP* dsp = add_dsp(handle, dsp_table, dsp_index);
            if (dsp == NULL)
                return false;

            // Create the DSP implementation
            char type[DSP_TYPE_LENGTH_MAX] = "";
            if (!Streader_read_string(sr, DSP_TYPE_LENGTH_MAX, type))
            {
                set_error(handle, sr);
                return false;
            }
            DSP_cons* cons = DSP_type_find_cons(type);
            if (cons == NULL)
            {
                Handle_set_error(handle, ERROR_FORMAT,
                        "Unsupported DSP type: %s", type);
                return false;
            }
            Device_impl* dsp_impl = cons(dsp);
            if (dsp_impl == NULL)
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory for DSP implementation");
                return false;
            }

            Device_set_impl((Device*)dsp, dsp_impl);

            // Remove old DSP Device state
            Device_states* dstates = Player_get_device_states(handle->player);
            Device_states_remove_state(dstates, Device_get_id((Device*)dsp));

            // Allocate Device state(s) for this DSP
            Device_state* ds = Device_create_state(
                    (Device*)dsp,
                    Player_get_audio_rate(handle->player),
                    Player_get_audio_buffer_size(handle->player));
            if (ds == NULL || !Device_states_add_state(
                        Player_get_device_states(handle->player), ds))
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory");
                del_Device_state(ds);
                del_DSP(dsp);
                return false;
            }

            // Set DSP resources
            if (!Device_set_audio_rate((Device*)dsp,
                        dstates,
                        Player_get_audio_rate(handle->player)) ||
                    !Device_set_buffer_size((Device*)dsp,
                        dstates,
                        Player_get_audio_buffer_size(handle->player)))
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory for DSP state");
                return false;
            }

            // Sync the DSP
            if (!Device_sync((Device*)dsp))
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory while syncing DSP");
                return false;
            }

            // Sync the Device state(s)
            if (!Device_sync_states(
                        (Device*)dsp,
                        Player_get_device_states(handle->player)))
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory while syncing DSP");
                return false;
            }
        }
    }
    else if ((string_has_prefix(subkey, "i/") ||
              string_has_prefix(subkey, "c/")) &&
             key_is_device_param(subkey))
    {
        DSP* dsp = add_dsp(handle, dsp_table, dsp_index);
        if (dsp == NULL)
            return false;

        // Update Device
        if (!Device_set_key((Device*)dsp, subkey, sr))
        {
            set_error(handle, sr);
            return false;
        }

        // Notify Device state
        Device_set_state_key(
                (Device*)dsp,
                Player_get_device_states(handle->player),
                subkey);
    }
#if 0
    else if (string_eq(subkey, "p_events.json"))
    {
        DSP* dsp = add_dsp(handle, dsp_table, dsp_index);
        if (dsp == NULL)
            return false;

        DSP_conf* conf = add_dsp_conf(handle, dsp_table, dsp_index);
        if (conf == NULL)
            return false;

        Read_state* state = Read_state_init(READ_STATE_AUTO, key);
        if (!Device_params_parse_events(
                    conf->params,
                    DEVICE_EVENT_TYPE_DSP,
                    handle->player,
                    data,
                    state))
        {
            set_parse_error(handle, state);
            return false;
        }
    }
#endif

    return true;
}


static bool parse_pattern_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr,
        int index)
{
//    fprintf(stderr, "pattern level: %s\n", key);
    assert(handle != NULL);
    assert(key != NULL);
    assert(subkey != NULL);
    assert(sr != NULL);

    if (index < 0 || index >= KQT_PATTERNS_MAX)
        return true;

    Module* module = Handle_get_module(handle);

    if (string_eq(subkey, "p_manifest.json"))
    {
        const bool existent = read_default_manifest(sr);
        if (Streader_is_error_set(sr))
        {
            set_error(handle, sr);
            return false;
        }
        Pat_table* pats = Module_get_pats(module);
        Pat_table_set_existent(pats, index, existent);
    }
    else if (string_eq(subkey, "p_pattern.json"))
    {
        Pattern* pat = Pat_table_get(Module_get_pats(module), index);
        bool new_pattern = pat == NULL;
        if (new_pattern)
        {
            pat = new_Pattern();
            if (pat == NULL)
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory");
                return false;
            }
        }

        if (!Pattern_parse_header(pat, sr))
        {
            set_error(handle, sr);
            if (new_pattern)
            {
                del_Pattern(pat);
            }
            return false;
        }
        if (new_pattern && !Pat_table_set(Module_get_pats(module), index, pat))
        {
            Handle_set_error(handle, ERROR_MEMORY,
                    "Couldn't allocate memory");
            del_Pattern(pat);
            return false;
        }
        return true;
    }

    char* second_element = strchr(subkey, '/');
    if (second_element == NULL)
        return true;

    int sub_index = 0;
    ++second_element;
    if ((sub_index = string_extract_index(subkey, "col_", 2, "/")) >= 0 &&
                string_eq(second_element, "p_triggers.json"))
    {
        if (sub_index >= KQT_COLUMNS_MAX)
            return true;

        Pattern* pat = Pat_table_get(Module_get_pats(module), index);
        bool new_pattern = pat == NULL;
        if (new_pattern)
        {
            pat = new_Pattern();
            if (pat == NULL)
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory");
                return false;
            }
        }
        const Event_names* event_names =
                Event_handler_get_names(Player_get_event_handler(handle->player));
        Column* col = new_Column_from_string(
                sr, Pattern_get_length(pat), event_names);
        if (col == NULL)
        {
            set_error(handle, sr);

            if (new_pattern)
                del_Pattern(pat);

            return false;
        }
        if (!Pattern_set_column(pat, sub_index, col))
        {
            Handle_set_error(handle, ERROR_MEMORY,
                    "Couldn't allocate memory");

            if (new_pattern)
                del_Pattern(pat);

            return false;
        }
        if (new_pattern)
        {
            if (!Pat_table_set(Module_get_pats(module), index, pat))
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory");
                del_Pattern(pat);
                return false;
            }
        }
    }
    else if ((sub_index = string_extract_index(subkey, "instance_", 3, "/")) >= 0)
    {
        Pattern* pat = Pat_table_get(Module_get_pats(module), index);
        bool new_pattern = (pat == NULL);
        if (new_pattern)
        {
            pat = new_Pattern();
            if (pat == NULL)
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory");
                return false;
            }
        }

        assert(pat != NULL);
        if (!parse_pat_inst_level(
                    handle,
                    pat,
                    key,
                    second_element,
                    sr,
                    sub_index))
        {
            if (new_pattern)
            {
                del_Pattern(pat);
            }
            return false;
        }

        if (new_pattern && !Pat_table_set(Module_get_pats(module), index, pat))
        {
            Handle_set_error(handle, ERROR_MEMORY,
                    "Couldn't allocate memory");
            del_Pattern(pat);
            return false;
        }
        return true;
    }

    return true;
}


static bool parse_pat_inst_level(
        Handle* handle,
        Pattern* pat,
        const char* key,
        const char* subkey,
        Streader* sr,
        int index)
{
    assert(handle != NULL);
    assert(key != NULL);
    assert(subkey != NULL);
    assert(sr != NULL);
    (void)key;

    if (string_eq(subkey, "p_manifest.json"))
    {
        const bool existent = read_default_manifest(sr);
        if (Streader_is_error_set(sr))
        {
            set_error(handle, sr);
            return false;
        }

        Pattern_set_inst_existent(pat, index, existent);
    }

    return true;
}


static bool parse_scale_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr,
        int index)
{
//    fprintf(stderr, "scale level: %s\n", key);
    assert(handle != NULL);
    assert(key != NULL);
    assert(subkey != NULL);
    assert(sr != NULL);
    (void)key;

    if (index < 0 || index >= KQT_SCALES_MAX)
        return true;

    Module* module = Handle_get_module(handle);

    if (string_eq(subkey, "p_scale.json"))
    {
        Scale* scale = new_Scale_from_string(sr);
        if (scale == NULL)
        {
            set_error(handle, sr);
            return false;
        }

        Module_set_scale(module, index, scale);
        return true;
    }

    return true;
}


static bool parse_subsong_level(
        Handle* handle,
        const char* key,
        const char* subkey,
        Streader* sr,
        int index)
{
//    fprintf(stderr, "subsong level: %s\n", key);
    assert(handle != NULL);
    assert(key != NULL);
    assert(subkey != NULL);
    assert(sr != NULL);
    (void)key;

    if (index < 0 || index >= KQT_SONGS_MAX)
        return true;

    Module* module = Handle_get_module(handle);

    if (string_eq(subkey, "p_manifest.json"))
    {
        const bool existent = read_default_manifest(sr);
        if (Streader_is_error_set(sr))
        {
            set_error(handle, sr);
            return false;
        }

        Song_table_set_existent(module->songs, index, existent);
    }
    else if (string_eq(subkey, "p_song.json"))
    {
        Song* song = new_Song_from_string(sr);
        if (song == NULL)
        {
            set_error(handle, sr);
            return false;
        }

        Song_table* st = Module_get_songs(module);
        if (!Song_table_set(st, index, song))
        {
            Handle_set_error(handle, ERROR_MEMORY,
                    "Couldn't allocate memory");
            del_Song(song);
            return false;
        }
    }
    else if (string_eq(subkey, "p_order_list.json"))
    {
        Order_list* ol = new_Order_list(sr);
        if (ol == NULL)
        {
            set_error(handle, sr);
            return false;
        }

        // Update pattern location information
        // This is required for correct update of jump counters.
#if 0
        const size_t ol_len = Order_list_get_len(ol);
        for (size_t i = 0; i < ol_len; ++i)
        {
            Pat_inst_ref* ref = Order_list_get_pat_inst_ref(ol, i);
            int16_t pat_index = ref->pat;
            Pat_table* pats = Module_get_pats(module);
            assert(pats != NULL);
            Pattern* pat = Pat_table_get(pats, pat_index);
            if (pat == NULL)
                continue;

            if (!Pattern_set_location(pat, index, ref))
            {
                Handle_set_error(handle, ERROR_MEMORY,
                        "Couldn't allocate memory");
                del_Order_list(ol);
                return false;
            }
        }
#endif

        if (module->order_lists[index] != NULL)
            del_Order_list(module->order_lists[index]);

        module->order_lists[index] = ol;
    }

    return true;
}


