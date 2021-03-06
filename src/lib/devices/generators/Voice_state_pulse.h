

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010-2014
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#ifndef K_VOICE_STATE_PULSE_H
#define K_VOICE_STATE_PULSE_H


#include <player/Voice_state.h>


typedef struct Voice_state_pulse
{
    Voice_state parent;
    double phase;
    double pulse_width;
} Voice_state_pulse;


/**
 * Initialise the Pulse generator parameters.
 *
 * \param pulse   The Pulse parameters -- must not be \c NULL.
 */
void Voice_state_pulse_init(Voice_state* state);


#endif // K_VOICE_STATE_PULSE_H


