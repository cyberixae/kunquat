

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
#include <stdbool.h>

#include <Event_common.h>
#include <Event_channel_set_instrument.h>
#include <File_base.h>
#include <Channel.h>
#include <Channel_state.h>
#include <kunquat/limits.h>
#include <xassert.h>
#include <xmemory.h>


static Event_field_desc set_instrument_desc[] =
{
    {
        .type = EVENT_FIELD_INT,
        .min.field.integral_type = 0,
        .max.field.integral_type = KQT_INSTRUMENTS_MAX - 1
    },
    {
        .type = EVENT_FIELD_NONE
    }
};


#if 0
Event_create_set_primitive_and_get(Event_channel_set_instrument,
                                   EVENT_CHANNEL_SET_INSTRUMENT,
                                   int64_t, instrument);
#endif


Event_create_constructor(Event_channel_set_instrument,
                         EVENT_CHANNEL_SET_INSTRUMENT,
                         set_instrument_desc/*,
                         event->instrument = 0*/);


bool Event_channel_set_instrument_process(Channel_state* ch_state, char* fields)
{
    assert(ch_state != NULL);
    if (fields == NULL)
    {
        return false;
    }
    Event_field data[1];
    Read_state* state = READ_STATE_AUTO;
    Event_type_get_fields(fields, set_instrument_desc, data, state);
    if (state->error)
    {
        return false;
    }
    ch_state->instrument = data[0].field.integral_type;
    return true;
}


