

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
#include <stdint.h>
#include <math.h>

#include <debug/assert.h>
#include <devices/Device_params.h>
#include <devices/generators/Generator_common.h>
#include <devices/generators/Generator_debug.h>
#include <memory.h>
#include <string/common.h>


typedef struct Generator_debug
{
    Device_impl parent;
    bool single_pulse;
} Generator_debug;


static bool Generator_debug_set_single_pulse(
        Device_impl* dimpl,
        Device_key_indices indices,
        bool value);

static uint32_t Generator_debug_mix(
        const Generator* gen,
        Gen_state* gen_state,
        Ins_state* ins_state,
        Voice_state* vstate,
        uint32_t nframes,
        uint32_t offset,
        uint32_t freq,
        double tempo);

static void del_Generator_debug(Device_impl* gen_impl);


Device_impl* new_Generator_debug(Generator* gen)
{
    Generator_debug* debug = memory_alloc_item(Generator_debug);
    if (debug == NULL)
        return NULL;

    if (!Device_impl_init(&debug->parent, del_Generator_debug))
    {
        memory_free(debug);
        return NULL;
    }

    debug->parent.device = (Device*)gen;

    gen->mix = Generator_debug_mix;

    if (!Device_impl_register_set_bool(
                &debug->parent,
                "p_b_single_pulse.json",
                false,
                Generator_debug_set_single_pulse,
                NULL))
    {
        del_Generator_debug(&debug->parent);
        return NULL;
    }

    debug->single_pulse = false;

    return &debug->parent;
}


static uint32_t Generator_debug_mix(
        const Generator* gen,
        Gen_state* gen_state,
        Ins_state* ins_state,
        Voice_state* vstate,
        uint32_t nframes,
        uint32_t offset,
        uint32_t freq,
        double tempo)
{
    assert(gen != NULL);
    //assert(string_eq(gen->type, "debug"));
    assert(gen_state != NULL);
    assert(ins_state != NULL);
    assert(vstate != NULL);
    assert(freq > 0);
    assert(tempo > 0);
    (void)ins_state;
    (void)tempo;

    kqt_frame* bufs[] = { NULL, NULL };
    Generator_common_get_buffers(gen_state, vstate, offset, bufs);

    if (!vstate->active)
        return offset;

    Generator_debug* debug = (Generator_debug*)gen->parent.dimpl;
    if (debug->single_pulse)
    {
        if (offset < nframes)
        {
            bufs[0][offset] += 1.0;
            bufs[1][offset] += 1.0;
            vstate->active = false;
            return offset + 1;
        }
        return offset;
    }

    for (uint32_t i = offset; i < nframes; ++i)
    {
        double vals[KQT_BUFFERS_MAX] = { 0 };

        if (vstate->rel_pos == 0)
        {
            vals[0] = vals[1] = 1.0;
            vstate->rel_pos = 1;
        }
        else
        {
            vals[0] = vals[1] = 0.5;
        }

        if (!vstate->note_on)
        {
            vals[0] = -vals[0];
            vals[1] = -vals[1];
        }

        vstate->actual_force = vstate->force * gen->ins_params->global_force;
        vals[0] *= vstate->actual_force;
        vals[1] *= vstate->actual_force;

        bufs[0][i] += vals[0];
        bufs[1][i] += vals[1];

        vstate->rel_pos_rem += vstate->pitch / freq;

        if (!vstate->note_on)
        {
            vstate->noff_pos_rem += vstate->pitch / freq;
            if (vstate->noff_pos_rem >= 2)
            {
                vstate->active = false;
                return i;
            }
        }

        if (vstate->rel_pos_rem >= 1)
        {
            ++vstate->pos;
            if (vstate->pos >= 10)
            {
                vstate->active = false;
                return i;
            }
            vstate->rel_pos = 0;
            vstate->rel_pos_rem -= floor(vstate->rel_pos_rem);
        }
    }

    return nframes;
}


static bool Generator_debug_set_single_pulse(
        Device_impl* dimpl,
        Device_key_indices indices,
        bool value)
{
    assert(dimpl != NULL);
    assert(indices != NULL);
    (void)indices;

    Generator_debug* debug = (Generator_debug*)dimpl;
    debug->single_pulse = value;

    return true;
}


static void del_Generator_debug(Device_impl* gen_impl)
{
    if (gen_impl == NULL)
        return;

    Generator_debug* debug = (Generator_debug*)gen_impl;
    memory_free(debug);

    return;
}


