

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


#ifndef K_EVENT_GENERATOR_SET_BOOL_H
#define K_EVENT_GENERATOR_SET_BOOL_H


#include <Event_generator.h>
#include <Generator.h>
#include <Reltime.h>


typedef struct Event_generator_set_bool
{
    Event_generator parent;
//    bool value;
} Event_generator_set_bool;


Event* new_Event_generator_set_bool(Reltime* pos);


bool Event_generator_set_bool_process(Generator* gen, char* fields);


#endif // K_EVENT_GENERATOR_SET_BOOL_H


