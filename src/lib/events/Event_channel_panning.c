

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010-2013
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
#include <math.h>

#include <Event_channel_decl.h>
#include <Event_common.h>
#include <Value.h>
#include <Voice.h>
#include <xassert.h>


bool Event_channel_set_panning_process(Channel_state* ch_state, Value* value)
{
    assert(ch_state != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_FLOAT)
    {
        return false;
    }
    ch_state->panning = value->value.float_type;
    Slider_break(&ch_state->panning_slider);
//    ch_state->panning_slide = 0;
    for (int i = 0; i < KQT_GENERATORS_MAX; ++i)
    {
        Event_check_voice(ch_state, i);
        Voice_state* vs = ch_state->fg[i]->state;
        vs->panning = ch_state->panning;
        Slider_break(&vs->panning_slider);
//        vs->panning_slide = 0;
    }
    return true;
}


bool Event_channel_slide_panning_process(
        Channel_state* ch_state,
        Value* value)
{
    assert(ch_state != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_FLOAT)
    {
        return false;
    }
    if (Slider_in_progress(&ch_state->panning_slider))
    {
        Slider_change_target(
                &ch_state->panning_slider,
                value->value.float_type);
    }
    else
    {
        Slider_start(
                &ch_state->panning_slider,
                value->value.float_type,
                ch_state->panning);
    }
    for (int i = 0; i < KQT_GENERATORS_MAX; ++i)
    {
        Event_check_voice(ch_state, i);
        Voice_state* vs = ch_state->fg[i]->state;
        Slider_copy(&vs->panning_slider, &ch_state->panning_slider);
    }
    return true;
}


bool Event_channel_slide_panning_length_process(
        Channel_state* ch_state,
        Value* value)
{
    assert(ch_state != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_TSTAMP)
    {
        return false;
    }
    Slider_set_length(
            &ch_state->panning_slider,
            &value->value.Tstamp_type);
    for (int i = 0; i < KQT_GENERATORS_MAX; ++i)
    {
        Event_check_voice(ch_state, i);
        Voice_state* vs = ch_state->fg[i]->state;
        Slider_set_length(&vs->panning_slider, &value->value.Tstamp_type);
    }
    return true;
}

