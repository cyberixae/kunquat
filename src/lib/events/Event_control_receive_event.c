

/*
 * Author: Tomi Jylhä-Ollila, Finland 2011-2012
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

#include <Event.h>
#include <Event_common.h>
#include <Event_control_receive_event.h>
#include <Event_names.h>
#include <Event_type.h>
#include <File_base.h>
#include <General_state.h>
#include <Playdata.h>
#include <Value.h>
#include <xassert.h>


bool Event_control_receive_event(General_state* gstate, Value* value)
{
    assert(gstate != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_STRING || !gstate->global)
    {
        return false;
    }
    Playdata* global_state = (Playdata*)gstate;
    if (global_state->event_filter != NULL)
    {
        Event_names_set_pass(global_state->event_filter,
                             value->value.string_type, true);
    }
    return true;
}

