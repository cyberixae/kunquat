

/*
 * Copyright 2009 Tomi Jylhä-Ollila
 *
 * This file is part of Kunquat.
 *
 * Kunquat is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Kunquat is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Kunquat.  If not, see <http://www.gnu.org/licenses/>.
 */


#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <math.h>

#include <Generator.h>
#include <Generator_common.h>
#include <Generator_sawtooth.h>
#include <Voice_state_sawtooth.h>
#include <Song_limits.h>

#include <xmemory.h>


static bool Generator_sawtooth_read(Generator* gen, File_tree* tree, Read_state* state);

void Generator_sawtooth_init_state(Generator* gen, Voice_state* state);


Generator_sawtooth* new_Generator_sawtooth(Instrument_params* ins_params)
{
    assert(ins_params != NULL);
    Generator_sawtooth* sawtooth = xalloc(Generator_sawtooth);
    if (sawtooth == NULL)
    {
        return NULL;
    }
    Generator_init(&sawtooth->parent);
    sawtooth->parent.read = Generator_sawtooth_read;
    sawtooth->parent.destroy = del_Generator_sawtooth;
    sawtooth->parent.type = GEN_TYPE_SAWTOOTH;
    sawtooth->parent.init_state = Generator_sawtooth_init_state;
    sawtooth->parent.mix = Generator_sawtooth_mix;
    sawtooth->parent.ins_params = ins_params;
    return sawtooth;
}


static bool Generator_sawtooth_read(Generator* gen, File_tree* tree, Read_state* state)
{
    assert(gen != NULL);
    assert(gen->type == GEN_TYPE_SAWTOOTH);
    assert(tree != NULL);
    assert(state != NULL);
    (void)gen;
    (void)tree;
    if (state->error)
    {
        return false;
    }
    return true;
}


void Generator_sawtooth_init_state(Generator* gen, Voice_state* state)
{
    assert(gen != NULL);
    assert(gen->type == GEN_TYPE_SAWTOOTH);
    assert(state != NULL);
    Voice_state_init(state);
    Voice_state_sawtooth* sawtooth_state = (Voice_state_sawtooth*)state;
    sawtooth_state->phase = 0.25;
    return;
}


double sawtooth(double phase)
{
    return (phase * 2) - 1;
} 


uint32_t Generator_sawtooth_mix(Generator* gen,
                                Voice_state* state,
                                uint32_t nframes,
                                uint32_t offset,
                                uint32_t freq,
                                int buf_count,
                                kqt_frame** bufs)
{
    assert(gen != NULL);
    assert(gen->type == GEN_TYPE_SAWTOOTH);
    assert(state != NULL);
//  assert(nframes <= ins->buf_len); XXX: Revisit after adding instrument buffers
    assert(freq > 0);
    assert(buf_count > 0);
    assert(bufs != NULL);
    assert(bufs[0] != NULL);
    Generator_common_check_active(gen, state, offset);
//    double max_amp = 0;
//  fprintf(stderr, "bufs are %p and %p\n", ins->bufs[0], ins->bufs[1]);
    Voice_state_sawtooth* sawtooth_state = (Voice_state_sawtooth*)state;
    for (uint32_t i = offset; i < nframes; ++i)
    {
        double vals[BUF_COUNT_MAX] = { 0 };
        vals[0] = vals[1] = sawtooth(sawtooth_state->phase) / 6;
        Generator_common_ramp_attack(gen, state, vals, 2, freq);
        sawtooth_state->phase += state->freq / freq;
        if (sawtooth_state->phase >= 1)
        {
            sawtooth_state->phase -= floor(sawtooth_state->phase);
        }
        state->pos = 1; // XXX: hackish
        Generator_common_handle_note_off(gen, state, vals, 2, freq, i);
        bufs[0][i] += vals[0];
        bufs[1][i] += vals[1];
/*        if (fabs(val_l) > max_amp)
        {
            max_amp = fabs(val_l);
        } */
    }
//  fprintf(stderr, "max_amp is %lf\n", max_amp);
    return nframes;
}


void del_Generator_sawtooth(Generator* gen)
{
    assert(gen != NULL);
    assert(gen->type == GEN_TYPE_SAWTOOTH);
    Generator_sawtooth* sawtooth = (Generator_sawtooth*)gen;
    xfree(sawtooth);
    return;
}


