

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
#include <stdio.h>
#include <stdbool.h>
#include <limits.h>

#include <Event_common.h>
#include <Event_global_pattern_delay.h>
#include <File_base.h>
#include <kunquat/limits.h>
#include <Value.h>
#include <xassert.h>
#include <xmemory.h>


#if 0
static Event_field_desc pattern_delay_desc[] =
{
    {
        .type = EVENT_FIELD_RELTIME,
        .min.field.Reltime_type = { 0, 0 },
        .max.field.Reltime_type = { INT64_MAX, KQT_RELTIME_BEAT - 1 }
    },
    {
        .type = EVENT_FIELD_NONE
    }
};
#endif


Event_create_constructor(Event_global,
                         EVENT_GLOBAL_PATTERN_DELAY,
                         pattern_delay);


bool Event_global_pattern_delay_process(Playdata* global_state, Value* value)
{
    assert(global_state != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_TIMESTAMP)
    {
        return false;
    }
    global_state->delay_event_index = global_state->event_index;
    Reltime_copy(&global_state->delay_left, &value->value.Timestamp_type);
    return true;
}


