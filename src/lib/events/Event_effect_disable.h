

/*
 * Author: Tomi Jylhä-Ollila, Finland 2011
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#ifndef K_EVENT_EFFECT_DISABLE_H
#define K_EVENT_EFFECT_DISABLE_H


#include <Event_effect.h>
#include <Reltime.h>


Event* new_Event_effect_disable(Reltime* pos);


bool Event_effect_disable_process(Effect* eff, char* fields);


#endif // K_EVENT_EFFECT_DISABLE_H


