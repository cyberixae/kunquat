

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


#ifndef K_EVENT_VOICE_TREMOLO_DEPTH_H
#define K_EVENT_VOICE_TREMOLO_DEPTH_H


#include <Event_voice.h>
#include <Reltime.h>


typedef struct Event_voice_tremolo_depth
{
    Event_voice parent;
    double depth;
} Event_voice_tremolo_depth;


Event* new_Event_voice_tremolo_depth(Reltime* pos);


#endif // K_EVENT_VOICE_TREMOLO_DEPTH_H


