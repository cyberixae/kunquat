

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


#ifndef K_VOICE_STATE_PCM_H
#define K_VOICE_STATE_PCM_H


#include <player/Voice_state.h>


typedef struct Voice_state_pcm
{
    Voice_state parent;
    int sample;
    double cents;
    double freq;
    double volume;
    uint8_t source;
    uint8_t expr;
    double middle_tone;
} Voice_state_pcm;


#endif // K_VOICE_STATE_PCM_H


