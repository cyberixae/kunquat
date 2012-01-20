

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
#include <math.h>

#include <Event_common.h>
#include <Event_general.h>
#include <Event_general_call_float.h>
#include <General_state.h>
#include <Value.h>
#include <xassert.h>
#include <xmemory.h>


static Event_field_desc call_float_desc[] =
{
    {
        .type = EVENT_FIELD_DOUBLE,
        .min.field.double_type = -INFINITY,
        .max.field.double_type = INFINITY
    },
    {
        .type = EVENT_FIELD_NONE
    }
};


Event_create_constructor(Event_general,
                         EVENT_GENERAL_CALL_FLOAT,
                         call_float);


bool Event_general_call_float_process(General_state* gstate, Value* value)
{
    assert(gstate != NULL);
    assert(value != NULL);
    return value->type == VALUE_TYPE_FLOAT;
}


