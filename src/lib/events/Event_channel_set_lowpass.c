

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010-2012
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

#include <Event_common.h>
#include <Event_channel_set_lowpass.h>
#include <Reltime.h>
#include <Value.h>
#include <Voice.h>
#include <xassert.h>
#include <xmemory.h>


bool Event_channel_set_lowpass_process(Channel_state* ch_state, Value* value)
{
    assert(ch_state != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_FLOAT)
    {
        return false;
    }
    double cutoff = NAN;
    if (value->value.float_type > 86)
    {
        cutoff = INFINITY;
    }
    else
    {
        cutoff = exp2((value->value.float_type + 86) / 12);
    }
    for (int i = 0; i < KQT_GENERATORS_MAX; ++i)
    {
        Event_check_voice(ch_state, i);
        Voice_state* vs = ch_state->fg[i]->state;
        vs->lowpass = cutoff;
    }
    return true;
}

