

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include <math.h>

#include <Event_common.h>
#include <Event_channel_set_panning.h>
#include <Reltime.h>
#include <Voice.h>

#include <xmemory.h>


static Event_field_desc set_panning_desc[] =
{
    {
        .type = EVENT_FIELD_DOUBLE,
        .min.field.double_type = -1,
        .max.field.double_type = 1
    },
    {
        .type = EVENT_FIELD_NONE
    }
};


Event_create_set_primitive_and_get(Event_channel_set_panning,
                                   EVENT_CHANNEL_SET_PANNING,
                                   double, panning);


Event_create_constructor(Event_channel_set_panning,
                         EVENT_CHANNEL_SET_PANNING,
                         set_panning_desc,
                         event->panning = 0);


bool Event_channel_set_panning_process(Channel_state* ch_state, char* fields)
{
    assert(ch_state != NULL);
    if (fields == NULL)
    {
        return false;
    }
    Event_field data[1];
    Read_state* state = READ_STATE_AUTO;
    Event_type_get_fields(fields, set_panning_desc, data, state);
    if (state->error)
    {
        return false;
    }
    ch_state->panning = data[0].field.double_type;
    ch_state->panning_slide = 0;
    for (int i = 0; i < KQT_GENERATORS_MAX; ++i)
    {
        Event_check_voice(ch_state, i);
        Voice_state* vs = &ch_state->fg[i]->state.generic;
        vs->panning = ch_state->panning;
        vs->panning_slide = 0;
    }
    return true;
}

