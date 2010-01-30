

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
#include <limits.h>

#include <Event_common.h>
#include <Event_global_pattern_delay.h>
#include <File_base.h>
#include <kunquat/limits.h>

#include <xmemory.h>


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


Event_create_set_reltime_and_get(Event_global_pattern_delay,
                                 EVENT_GLOBAL_PATTERN_DELAY,
                                 length)


static void Event_global_pattern_delay_process(Event_global* event, Playdata* play);


Event_create_constructor(Event_global_pattern_delay,
                         EVENT_GLOBAL_PATTERN_DELAY,
                         pattern_delay_desc,
                         Reltime_init(&event->length))


bool Event_global_pattern_delay_handle(Playdata* global_state, char* fields)
{
    assert(global_state != NULL);
    if (fields == NULL)
    {
        return false;
    }
    Reltime* delay = RELTIME_AUTO;
    Read_state* state = READ_STATE_AUTO;
    char* str = read_const_char(fields, '[', state);
    str = read_reltime(str, delay, state);
    str = read_const_char(str, ']', state);
    if (state->error)
    {
        return false;
    }
    Event_check_reltime_range(delay, pattern_delay_desc[0]);
    Reltime_copy(&global_state->delay_left, delay);
    return true;
}


static void Event_global_pattern_delay_process(Event_global* event, Playdata* play)
{
    assert(event != NULL);
    assert(event->parent.type == EVENT_GLOBAL_PATTERN_DELAY);
    assert(play != NULL);
    Event_global_pattern_delay* pattern_delay = (Event_global_pattern_delay*)event;
    Reltime_copy(&play->delay_left, &pattern_delay->length);
    return;
}


