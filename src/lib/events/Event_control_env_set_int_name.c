

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

#include <Event_common.h>
#include <Event_control.h>
#include <Event_control_env_set_int_name.h>
#include <Event_type.h>
#include <set_active_name.h>
#include <Value.h>
#include <xassert.h>


//static Event_field_desc* env_set_int_name_desc = set_name_desc;


Event_create_constructor(Event_control,
                         EVENT_CONTROL_ENV_SET_INT_NAME,
                         env_set_int_name);


bool Event_control_env_set_int_name_process(General_state* gstate,
                                            Value* value)
{
    assert(gstate != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_STRING || !gstate->global)
    {
        return false;
    }
    return set_active_name(gstate, ACTIVE_CAT_ENV, ACTIVE_TYPE_INT, value);
}


