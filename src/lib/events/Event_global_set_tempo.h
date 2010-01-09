

/*
 * Author: Tomi Jylhä-Ollila, Finland, 2010
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat waivers have waived all
 * copyright and related or neighboring rights to Kunquat. This work
 * is published from Finland.
 */


#ifndef K_EVENT_GLOBAL_SET_TEMPO_H
#define K_EVENT_GLOBAL_SET_TEMPO_H


#include <Event_global.h>
#include <Reltime.h>


typedef struct Event_global_set_tempo
{
    Event_global parent;
    double tempo;
} Event_global_set_tempo;


Event* new_Event_global_set_tempo(Reltime* pos);


#endif // K_EVENT_GLOBAL_SET_TEMPO_H


