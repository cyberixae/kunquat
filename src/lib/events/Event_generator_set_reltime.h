

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


#ifndef K_EVENT_GENERATOR_SET_RELTIME_H
#define K_EVENT_GENERATOR_SET_RELTIME_H


#include <Channel_state.h>
#include <Event_generator.h>
#include <Generator.h>
#include <Reltime.h>
#include <Value.h>


Event* new_Event_generator_set_reltime(Reltime* pos);


bool Event_generator_set_reltime_process(Generator* gen,
                                         Channel_state* ch_state,
                                         Value* value);


#endif // K_EVENT_GENERATOR_SET_RELTIME_H


