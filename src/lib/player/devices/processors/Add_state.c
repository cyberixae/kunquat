

/*
 * Author: Tomi Jylhä-Ollila, Finland 2015-2016
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <player/devices/processors/Add_state.h>

#include <debug/assert.h>
#include <init/devices/processors/Proc_add.h>
#include <mathnum/common.h>
#include <mathnum/conversions.h>
#include <mathnum/Random.h>
#include <player/devices/processors/Proc_state_utils.h>
#include <player/Work_buffers.h>

#include <stdint.h>
#include <stdlib.h>


#define ADD_BASE_FUNC_SIZE_MASK (ADD_BASE_FUNC_SIZE - 1)


typedef struct Add_tone_state
{
    double phase[2];
} Add_tone_state;


typedef struct Add_vstate
{
    Voice_state parent;
    int tone_limit;
    Add_tone_state tones[ADD_TONES_MAX];
} Add_vstate;


int32_t Add_vstate_get_size(void)
{
    return sizeof(Add_vstate);
}


enum
{
    PORT_IN_PITCH = 0,
    PORT_IN_FORCE,
    PORT_IN_PHASE_MOD_L,
    PORT_IN_PHASE_MOD_R,
    PORT_IN_COUNT
};

enum
{
    PORT_OUT_AUDIO_L = 0,
    PORT_OUT_AUDIO_R,
    PORT_OUT_COUNT
};


static const int ADD_WORK_BUFFER_FIXED_PITCH = WORK_BUFFER_IMPL_1;
static const int ADD_WORK_BUFFER_FIXED_FORCE = WORK_BUFFER_IMPL_2;
static const int ADD_WORK_BUFFER_MOD_L = WORK_BUFFER_IMPL_3;
static const int ADD_WORK_BUFFER_MOD_R = WORK_BUFFER_IMPL_4;


static int32_t Add_vstate_render_voice(
        Voice_state* vstate,
        Proc_state* proc_state,
        const Au_state* au_state,
        const Work_buffers* wbs,
        int32_t buf_start,
        int32_t buf_stop,
        double tempo)
{
    rassert(vstate != NULL);
    rassert(proc_state != NULL);
    rassert(au_state != NULL);
    rassert(wbs != NULL);
    rassert(tempo > 0);

    const Device_state* dstate = &proc_state->parent;
    const Proc_add* add = (Proc_add*)proc_state->parent.device->dimpl;
    Add_vstate* add_state = (Add_vstate*)vstate;
    rassert(is_p2(ADD_BASE_FUNC_SIZE));

    // Get frequencies
    Work_buffer* freqs_wb = Proc_state_get_voice_buffer_mut(
            proc_state, DEVICE_PORT_TYPE_RECEIVE, PORT_IN_PITCH);
    Work_buffer* pitches_wb = freqs_wb;
    if (freqs_wb == NULL)
        freqs_wb = Work_buffers_get_buffer_mut(wbs, ADD_WORK_BUFFER_FIXED_PITCH);
    Proc_fill_freq_buffer(freqs_wb, pitches_wb, buf_start, buf_stop);
    const float* freqs = Work_buffer_get_contents(freqs_wb);

    // Get volume scales
    Work_buffer* scales_wb = Proc_state_get_voice_buffer_mut(
            proc_state, DEVICE_PORT_TYPE_RECEIVE, PORT_IN_FORCE);
    Work_buffer* dBs_wb = scales_wb;
    if (scales_wb == NULL)
        scales_wb = Work_buffers_get_buffer_mut(wbs, ADD_WORK_BUFFER_FIXED_FORCE);
    Proc_fill_scale_buffer(scales_wb, dBs_wb, buf_start, buf_stop);
    const float* scales = Work_buffer_get_contents(scales_wb);

    // Get output buffer for writing
    float* out_bufs[2] = { NULL };
    Proc_state_get_voice_audio_out_buffers(
            proc_state, PORT_OUT_AUDIO_L, PORT_OUT_COUNT, out_bufs);

    // Get phase modulation signal
    float* mod_values[] =
    {
        Work_buffers_get_buffer_contents_mut(wbs, ADD_WORK_BUFFER_MOD_L),
        Work_buffers_get_buffer_contents_mut(wbs, ADD_WORK_BUFFER_MOD_R),
    };

    {
        // Copy from the input voice buffers if available
        // XXX: not sure if the best way to handle this...

        float* in_mod_bufs[2] = { NULL };
        Proc_state_get_voice_audio_in_buffers(
                proc_state, PORT_IN_PHASE_MOD_L, PORT_IN_COUNT, in_mod_bufs);

        for (int ch = 0; ch < 2; ++ch)
        {
            const float* mod_in_values = in_mod_bufs[ch];

            if (mod_in_values != NULL)
            {
                float* mod_values_ch = mod_values[ch];
                for (int32_t i = buf_start; i < buf_stop; ++i)
                    mod_values_ch[i] = mod_in_values[i];
            }
            else
            {
                float* mod_values_ch = mod_values[ch];
                for (int32_t i = buf_start; i < buf_stop; ++i)
                    mod_values_ch[i] = 0;
            }
        }
    }

    // Add base waveform tones
    const double inv_audio_rate = 1.0 / dstate->audio_rate;

    const float* base = Sample_get_buffer(add->base, 0);

    for (int h = 0; h < add_state->tone_limit; ++h)
    {
        const Add_tone* tone = &add->tones[h];
        const double pitch_factor = tone->pitch_factor;
        const double volume_factor = tone->volume_factor;

        if ((pitch_factor <= 0) || (volume_factor <= 0))
            continue;

        const double pannings[] =
        {
            -tone->panning,
            tone->panning,
        };

        const double pitch_factor_inv_audio_rate = pitch_factor * inv_audio_rate;

        Add_tone_state* tone_state = &add_state->tones[h];

        for (int32_t ch = 0; ch < 2; ++ch)
        {
            float* out_buf_ch = out_bufs[ch];
            if (out_buf_ch == NULL)
                continue;

            const double panning_factor = 1 + pannings[ch];
            const float* mod_values_ch = mod_values[ch];

            double phase = tone_state->phase[ch];

            for (int32_t i = buf_start; i < buf_stop; ++i)
            {
                const float freq = freqs[i];
                const float vol_scale = scales[i];
                const float mod_val = mod_values_ch[i];

                // Note: + mod_val is specific to phase modulation
                const double actual_phase = phase + mod_val;
                const double pos = actual_phase * ADD_BASE_FUNC_SIZE;

                // Note: direct cast of negative doubles to uint32_t is undefined
                const uint32_t pos1 = (uint32_t)(int32_t)pos & ADD_BASE_FUNC_SIZE_MASK;
                const uint32_t pos2 = pos1 + 1;

                const float item1 = base[pos1];
                const float item_diff = base[pos2] - item1;
                const double lerp_val = pos - floor(pos);
                const double value =
                    (item1 + (lerp_val * item_diff)) * volume_factor * panning_factor;

                out_buf_ch[i] += (float)value * vol_scale;

                phase += freq * pitch_factor_inv_audio_rate;

                // Normalise to range [0, 1)
                if (phase >= 1)
                {
                    phase -= 1;

                    // Don't bother updating the phase if our frequency is too high
                    if (phase >= 1)
                        phase = tone_state->phase[ch];
                }
            }

            tone_state->phase[ch] = phase;
        }
    }

    if (add->is_ramp_attack_enabled)
        Proc_ramp_attack(vstate, 2, out_bufs, buf_start, buf_stop, dstate->audio_rate);

    return buf_stop;
}


void Add_vstate_init(Voice_state* vstate, const Proc_state* proc_state)
{
    rassert(vstate != NULL);
    rassert(proc_state != NULL);

    vstate->render_voice = Add_vstate_render_voice;

    Proc_add* add = (Proc_add*)proc_state->parent.device->dimpl;
    Add_vstate* add_state = (Add_vstate*)vstate;

    add_state->tone_limit = 0;

    for (int h = 0; h < ADD_TONES_MAX; ++h)
    {
        if (add->tones[h].pitch_factor <= 0 ||
                add->tones[h].volume_factor <= 0)
            continue;

        add_state->tone_limit = h + 1;

        const double phase =
            add->is_rand_phase_enabled ? Random_get_float_lb(vstate->rand_p) : 0;

        for (int ch = 0; ch < 2; ++ch)
            add_state->tones[h].phase[ch] = phase;
    }

    return;
}


