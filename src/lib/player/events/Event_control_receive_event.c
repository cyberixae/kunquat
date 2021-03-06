

/*
 * Author: Tomi Jylhä-Ollila, Finland 2011-2014
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

#include <debug/assert.h>
#include <player/Event_names.h>
#include <player/Event_type.h>
#include <player/events/Event_common.h>
#include <player/events/Event_control_decl.h>
#include <player/General_state.h>
#include <Value.h>


bool Event_control_receive_event_process(General_state* gstate, const Value* value)
{
    assert(gstate != NULL);
    assert(value != NULL);
    assert(value->type == VALUE_TYPE_STRING);
    (void)value;

    if (!gstate->global)
        return false;

    return false;

#if 0
    Playdata* global_state = (Playdata*)gstate;
    if (global_state->event_filter != NULL)
    {
        Event_names_set_pass(
                global_state->event_filter,
                value->value.string_type, true);
    }
    return true;
#endif
}


