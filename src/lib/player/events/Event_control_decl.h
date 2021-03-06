

/*
 * Author: Tomi Jylhä-Ollila, Finland 2013-2014
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#ifndef K_EVENT_CONTROL_DECL_H
#define K_EVENT_CONTROL_DECL_H


#include <stdbool.h>

#include <player/General_state.h>
#include <Value.h>


// Process function declarations

#define EVENT_CONTROL_DEF(name, type_suffix, arg_type, validator) \
    bool Event_control_##type_suffix##_process(General_state* gstate, const Value* value);
#include <player/events/Event_control_types.h>


#endif // K_EVENT_CONTROL_DECL_H


