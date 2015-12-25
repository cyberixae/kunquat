

/*
 * Author: Tomi Jylhä-Ollila, Finland 2011-2015
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <devices/processors/Proc_delay.h>

#include <Audio_buffer.h>
#include <debug/assert.h>
#include <devices/Device_impl.h>
#include <devices/Processor.h>
#include <devices/processors/Proc_utils.h>
#include <mathnum/common.h>
#include <memory.h>
#include <string/common.h>

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#define MAX_BUF_TIME 60

#define DB_MAX 18
#define TAPS_MAX 32


typedef struct Tap_state
{
    bool enabled;
    int32_t buf_pos;
    int32_t frames_left;
    double scale;
} Tap_state;


typedef struct Delay_state
{
    Proc_state parent;

    Audio_buffer* buf;
    int32_t buf_pos;
    Tap_state tap_states[TAPS_MAX];
} Delay_state;


typedef struct Tap
{
    double delay;
    double scale;
} Tap;


typedef struct Proc_delay
{
    Device_impl parent;

    double max_delay;
    Tap taps[TAPS_MAX];
} Proc_delay;


static void Tap_state_set(
        Tap_state* tstate,
        double delay,
        double scale,
        int32_t master_buf_pos,
        int32_t buf_size,
        int32_t audio_rate)
{
    assert(tstate != NULL);
    assert(isfinite(scale));
    assert(master_buf_pos < buf_size);
    assert(buf_size > 0);
    assert(audio_rate > 0);

    if (!isfinite(delay) || (delay < 0))
    {
        tstate->enabled = false;
        return;
    }

    tstate->enabled = true;
    tstate->frames_left = 0;

    const int32_t delay_frames = delay * audio_rate;
    assert(delay_frames >= 0);
    assert(delay_frames <= buf_size);
    tstate->buf_pos = (buf_size + master_buf_pos - delay_frames) % buf_size;
    assert(tstate->buf_pos >= 0);

    tstate->scale = scale;

    return;
}


static void Delay_state_reset(Device_state* dstate)
{
    assert(dstate != NULL);

    Delay_state* dlstate = (Delay_state*)dstate;
    const Proc_delay* delay = (const Proc_delay*)dstate->device->dimpl;

    Audio_buffer_clear(dlstate->buf, 0, Audio_buffer_get_size(dlstate->buf));
    dlstate->buf_pos = 0;

    const int32_t audio_rate = dlstate->parent.parent.audio_rate;
    const int32_t buf_size = Audio_buffer_get_size(dlstate->buf);

    for (int i = 0; i < TAPS_MAX; ++i)
    {
        const Tap* tap = &delay->taps[i];
        Tap_state* tstate = &dlstate->tap_states[i];

        Tap_state_set(
                tstate, tap->delay, tap->scale, dlstate->buf_pos, buf_size, audio_rate);
    }

    return;
}


static bool Delay_state_set_audio_rate(Device_state* dstate, int32_t audio_rate)
{
    assert(dstate != NULL);
    assert(audio_rate > 0);

    Delay_state* dlstate = (Delay_state*)dstate;
    const Proc_delay* delay = (const Proc_delay*)dstate->device->dimpl;

    assert(dlstate->buf != NULL);
    long buf_len =
        max(Audio_buffer_get_size(dlstate->buf), delay->max_delay * audio_rate);
    assert(buf_len > 0);
    buf_len += 1; // so that the maximum delay will work

    if (!Audio_buffer_resize(dlstate->buf, buf_len))
        return false;

    Delay_state_reset(dstate);

    return true;
}


static void Delay_state_deinit(Device_state* dev_state)
{
    assert(dev_state != NULL);

    Delay_state* dlstate = (Delay_state*)dev_state;
    if (dlstate->buf != NULL)
    {
        del_Audio_buffer(dlstate->buf);
        dlstate->buf = NULL;
    }

    Proc_state_deinit(&dlstate->parent.parent);

    return;
}


static bool Proc_delay_init(Device_impl* dimpl);

static Device_state* Proc_delay_create_state(
        const Device* device, int32_t audio_rate, int32_t audio_buffer_size);

static Set_float_func Proc_delay_set_max_delay;
static Set_float_func Proc_delay_set_tap_delay;
static Set_float_func Proc_delay_set_tap_volume;

static Set_state_float_func Proc_delay_set_state_max_delay;
static Set_state_float_func Proc_delay_set_state_tap_delay;
static Set_state_float_func Proc_delay_set_state_tap_volume;

static void Delay_state_clear_history(Proc_state* proc_state);

static void Delay_state_render_mixed(
        Device_state* dstate,
        const Work_buffers* wbs,
        int32_t buf_start,
        int32_t buf_stop,
        double tempo);

static void del_Proc_delay(Device_impl* dimpl);


Device_impl* new_Proc_delay(Processor* proc)
{
    Proc_delay* delay = memory_alloc_item(Proc_delay);
    if (delay == NULL)
        return NULL;

    delay->parent.device = (Device*)proc;

    Device_impl_register_init(&delay->parent, Proc_delay_init);
    Device_impl_register_destroy(&delay->parent, del_Proc_delay);

    return &delay->parent;
}


static bool Proc_delay_init(Device_impl* dimpl)
{
    assert(dimpl != NULL);

    Proc_delay* delay = (Proc_delay*)dimpl;

    Device_set_state_creator(delay->parent.device, Proc_delay_create_state);

    // Register key handlers
    bool reg_success = true;

    reg_success &= Device_impl_register_set_float(
            &delay->parent,
            "p_f_max_delay.json",
            2.0,
            Proc_delay_set_max_delay,
            Proc_delay_set_state_max_delay);
    reg_success &= Device_impl_register_set_float(
            &delay->parent,
            "tap_XX/p_f_delay.json",
            -1.0,
            Proc_delay_set_tap_delay,
            Proc_delay_set_state_tap_delay);
    reg_success &= Device_impl_register_set_float(
            &delay->parent,
            "tap_XX/p_f_volume.json",
            0.0,
            Proc_delay_set_tap_volume,
            Proc_delay_set_state_tap_volume);

    if (!reg_success)
        return false;

    // TODO: add control variable accessors

    delay->max_delay = 2;

    for (int i = 0; i < TAPS_MAX; ++i)
    {
        delay->taps[i].delay = INFINITY;
        delay->taps[i].scale = 1;
    }

    return true;
}


static Device_state* Proc_delay_create_state(
        const Device* device, int32_t audio_rate, int32_t audio_buffer_size)
{
    assert(device != NULL);
    assert(audio_rate > 0);
    assert(audio_buffer_size >= 0);

    Delay_state* dlstate = memory_alloc_item(Delay_state);
    if (dlstate == NULL)
        return NULL;

    if (!Proc_state_init(&dlstate->parent, device, audio_rate, audio_buffer_size))
    {
        memory_free(dlstate);
        return NULL;
    }

    const Proc_delay* delay = (Proc_delay*)device->dimpl;

    dlstate->parent.parent.deinit = Delay_state_deinit;
    dlstate->parent.set_audio_rate = Delay_state_set_audio_rate;
    dlstate->parent.reset = Delay_state_reset;
    dlstate->parent.render_mixed = Delay_state_render_mixed;
    dlstate->parent.clear_history = Delay_state_clear_history;
    dlstate->buf = NULL;

    dlstate->buf = new_Audio_buffer(delay->max_delay * audio_rate + 1);
    if (dlstate->buf == NULL)
    {
        del_Device_state(&dlstate->parent.parent);
        return NULL;
    }

    dlstate->buf_pos = 0;

    for (int i = 0; i < TAPS_MAX; ++i)
    {
        Tap_state* tstate = &dlstate->tap_states[i];
        tstate->enabled = false;
        tstate->buf_pos = 0;
        tstate->frames_left = 0;
        tstate->scale = 1.0;
    }

    return &dlstate->parent.parent;
}


static double get_tap_delay(double value)
{
    return (value >= 0) ? value : INFINITY;
}

static double get_tap_volume(double value)
{
    return (isfinite(value) && value < DB_MAX) ? exp2(value / 6) : 1.0;
}


static bool Proc_delay_set_max_delay(
        Device_impl* dimpl, Key_indices indices, double value)
{
    assert(dimpl != NULL);
    assert(indices != NULL);

    Proc_delay* delay = (Proc_delay*)dimpl;
    delay->max_delay = min(value, MAX_BUF_TIME);

    return true;
}


static bool Proc_delay_set_tap_delay(
        Device_impl* dimpl, Key_indices indices, double value)
{
    assert(dimpl != NULL);
    assert(indices != NULL);

    if (indices[0] < 0 || indices[0] >= TAPS_MAX)
        return true;

    Proc_delay* delay = (Proc_delay*)dimpl;
    delay->taps[indices[0]].delay = get_tap_delay(value);

    return true;
}


static bool Proc_delay_set_tap_volume(
        Device_impl* dimpl, Key_indices indices, double value)
{
    assert(dimpl != NULL);
    assert(indices != NULL);

    if (indices[0] < 0 || indices[0] >= TAPS_MAX)
        return true;

    Proc_delay* delay = (Proc_delay*)dimpl;
    delay->taps[indices[0]].scale = get_tap_volume(value);

    return true;
}


static bool Proc_delay_set_state_max_delay(
        const Device_impl* dimpl,
        Device_state* dstate,
        Key_indices indices,
        double value)
{
    assert(dimpl != NULL);
    assert(dstate != NULL);
    assert(indices != NULL);

    Delay_state* dlstate = (Delay_state*)dstate;

    long buf_len = max(
            Audio_buffer_get_size(dlstate->buf),
            value * dstate->audio_rate + 1); // + 1 for maximum delay support
    assert(buf_len > 0);

    return Audio_buffer_resize(dlstate->buf, buf_len);
}


static bool Proc_delay_set_state_tap_delay(
        const Device_impl* dimpl,
        Device_state* dstate,
        Key_indices indices,
        double value)
{
    assert(dimpl != NULL);
    assert(dstate != NULL);
    assert(indices != NULL);
    assert(isfinite(value));

    if (indices[0] < 0 || indices[0] >= TAPS_MAX)
        return true;

    const Proc_delay* delay = (const Proc_delay*)dimpl;
    Delay_state* dlstate = (Delay_state*)dstate;
    Tap_state_set(
            &dlstate->tap_states[indices[0]],
            value,
            delay->taps[indices[0]].scale,
            dlstate->buf_pos,
            Audio_buffer_get_size(dlstate->buf),
            dstate->audio_rate);

    return true;
}


static bool Proc_delay_set_state_tap_volume(
        const Device_impl* dimpl,
        Device_state* dstate,
        Key_indices indices,
        double value)
{
    assert(dimpl != NULL);
    assert(dstate != NULL);
    assert(indices != NULL);
    assert(isfinite(value));

    if (indices[0] < 0 || indices[0] >= TAPS_MAX)
        return true;

    Delay_state* dlstate = (Delay_state*)dstate;
    dlstate->tap_states[indices[0]].scale = get_tap_volume(value);

    return true;
}


static void Delay_state_clear_history(Proc_state* proc_state)
{
    assert(proc_state != NULL);

    Delay_state* dlstate = (Delay_state*)proc_state;
    Audio_buffer_clear(dlstate->buf, 0, Audio_buffer_get_size(dlstate->buf));

    return;
}


static void Delay_state_render_mixed(
        Device_state* dstate,
        const Work_buffers* wbs,
        int32_t buf_start,
        int32_t buf_stop,
        double tempo)
{
    assert(dstate != NULL);
    assert(wbs != NULL);
    assert(buf_start >= 0);
    assert(buf_start <= buf_stop);
    assert(isfinite(tempo));
    assert(tempo > 0);

    Delay_state* dlstate = (Delay_state*)dstate;

    const Proc_delay* delay = (const Proc_delay*)dstate->device->dimpl;

    float* in_data[] = { NULL, NULL };
    float* out_data[] = { NULL, NULL };
    get_raw_input(&dlstate->parent.parent, 0, in_data);
    get_raw_output(&dlstate->parent.parent, 0, out_data);
    float* delay_data[] =
    {
        Audio_buffer_get_buffer(dlstate->buf, 0),
        Audio_buffer_get_buffer(dlstate->buf, 1)
    };

    const int32_t buf_size = Audio_buffer_get_size(dlstate->buf);
    const int32_t nframes = buf_stop - buf_start;

    for (int tap_index = 0; tap_index < TAPS_MAX; ++tap_index)
    {
        const Tap* tap = &delay->taps[tap_index];
        if (tap->delay > delay->max_delay)
            continue;

        Tap_state* tstate = &dlstate->tap_states[tap_index];

        int32_t delay_frames = dlstate->buf_pos - tstate->buf_pos;
        if (delay_frames < 0)
        {
            delay_frames += buf_size;
            assert(delay_frames > 0);
        }

        tstate->frames_left = nframes;
        const int32_t mix_until = min(delay_frames, nframes);

        for (int32_t i = 0; i < mix_until; ++i)
        {
            out_data[0][buf_start + i] +=
                delay_data[0][tstate->buf_pos] * tap->scale;
            out_data[1][buf_start + i] +=
                delay_data[1][tstate->buf_pos] * tap->scale;

            ++tstate->buf_pos;
            if (tstate->buf_pos >= buf_size)
            {
                assert(tstate->buf_pos == buf_size);
                tstate->buf_pos = 0;
            }
        }

        tstate->frames_left -= mix_until;
    }

    int32_t new_buf_pos = dlstate->buf_pos;

    for (int32_t i = buf_start; i < buf_stop; ++i)
    {
        delay_data[0][new_buf_pos] = in_data[0][i];
        delay_data[1][new_buf_pos] = in_data[1][i];

        ++new_buf_pos;
        if (new_buf_pos >= buf_size)
        {
            assert(new_buf_pos == buf_size);
            new_buf_pos = 0;
        }
    }

    for (int tap_index = 0; tap_index < TAPS_MAX; ++tap_index)
    {
        const Tap* tap = &delay->taps[tap_index];
        if (tap->delay > delay->max_delay)
            continue;

        Tap_state* tstate = &dlstate->tap_states[tap_index];

        for (int32_t i = nframes - tstate->frames_left; i < nframes; ++i)
        {
            out_data[0][buf_start + i] +=
                delay_data[0][tstate->buf_pos] * tap->scale;
            out_data[1][buf_start + i] +=
                delay_data[1][tstate->buf_pos] * tap->scale;

            ++tstate->buf_pos;
            if (tstate->buf_pos >= buf_size)
            {
                assert(tstate->buf_pos == buf_size);
                tstate->buf_pos = 0;
            }
        }
    }

    dlstate->buf_pos += nframes;
    if (dlstate->buf_pos >= buf_size)
    {
        dlstate->buf_pos -= buf_size;
        assert(dlstate->buf_pos >= 0);
        assert(dlstate->buf_pos < buf_size);
    }

    return;
}


static void del_Proc_delay(Device_impl* dimpl)
{
    if (dimpl == NULL)
        return;

    Proc_delay* delay = (Proc_delay*)dimpl;
    memory_free(delay);

    return;
}


