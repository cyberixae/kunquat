

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
#include <limits.h>

#include <Event_common.h>
#include <Event_global_set_jump_counter.h>
#include <kunquat/limits.h>
#include <Value.h>
#include <xassert.h>
#include <xmemory.h>


Event_create_constructor(Event_global,
                         EVENT_GLOBAL_SET_JUMP_COUNTER,
                         set_jump_counter);


bool Event_global_set_jump_counter_process(Playdata* global_state,
                                           Value* value)
{
    assert(global_state != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_INT)
    {
        return false;
    }
    global_state->jump_set_counter = value->value.int_type;
    return true;
}


