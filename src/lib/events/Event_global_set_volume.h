

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


#ifndef K_EVENT_GLOBAL_SET_VOLUME_H
#define K_EVENT_GLOBAL_SET_VOLUME_H


#include <Event_global.h>
#include <Reltime.h>


typedef struct Event_global_set_volume
{
    Event_global parent;
    double volume_dB;
} Event_global_set_volume;


Event* new_Event_global_set_volume(Reltime* pos);


bool Event_global_set_volume_process(Playdata* global_state, char* fields);


#endif // K_EVENT_GLOBAL_SET_VOLUME_H

