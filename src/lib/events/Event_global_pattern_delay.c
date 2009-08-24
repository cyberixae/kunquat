

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
#include <stdbool.h>
#include <limits.h>

#include <Event_common.h>
#include <Event_global_pattern_delay.h>
#include <kunquat/limits.h>

#include <xmemory.h>


static Event_field_desc pattern_delay_desc[] =
{
    {
        .type = EVENT_FIELD_RELTIME,
        .range.Reltime_type = { { 0, 0 }, { INT64_MAX, KQT_RELTIME_BEAT - 1 } }
    },
    {
        .type = EVENT_FIELD_NONE
    }
};


static bool Event_global_pattern_delay_set(Event* event, int index, void* data);

static void* Event_global_pattern_delay_get(Event* event, int index);

static void Event_global_pattern_delay_process(Event_global* event, Playdata* play);


Event* new_Event_global_pattern_delay(Reltime* pos)
{
    assert(pos != NULL);
    Event_global_pattern_delay* event = xalloc(Event_global_pattern_delay);
    if (event == NULL)
    {
        return NULL;
    }
    Event_init(&event->parent.parent,
               pos,
               EVENT_GLOBAL_PATTERN_DELAY,
               pattern_delay_desc,
               Event_global_pattern_delay_set,
               Event_global_pattern_delay_get);
    event->parent.process = Event_global_pattern_delay_process;
    Reltime_init(&event->length);
    return (Event*)event;
}


static bool Event_global_pattern_delay_set(Event* event, int index, void* data)
{
    assert(event != NULL);
    assert(event->type == EVENT_GLOBAL_PATTERN_DELAY);
    assert(data != NULL);
    Event_global_pattern_delay* pattern_delay = (Event_global_pattern_delay*)event;
    if (index == 0)
    {
        Reltime* length = data;
        Event_check_reltime_range(length, event->field_types[0]);
        Reltime_copy(&pattern_delay->length, length);
        return true;
    }
    return false;
}


static void* Event_global_pattern_delay_get(Event* event, int index)
{
    assert(event != NULL);
    assert(event->type == EVENT_GLOBAL_PATTERN_DELAY);
    Event_global_pattern_delay* pattern_delay = (Event_global_pattern_delay*)event;
    if (index == 0)
    {
        return &pattern_delay->length;
    }
    return NULL;
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


