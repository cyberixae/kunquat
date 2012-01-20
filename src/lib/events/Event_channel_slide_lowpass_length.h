

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


#ifndef K_EVENT_CHANNEL_SLIDE_LOWPASS_LENGTH_H
#define K_EVENT_CHANNEL_SLIDE_LOWPASS_LENGTH_H


#include <Event_channel.h>
#include <Reltime.h>
#include <Value.h>


Event* new_Event_channel_slide_lowpass_length(Reltime* pos);


bool Event_channel_slide_lowpass_length_process(Channel_state* ch_state,
                                                Value* value);


#endif // K_EVENT_CHANNEL_SLIDE_LOWPASS_LENGTH_H


