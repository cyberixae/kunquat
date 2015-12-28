

/*
 * Author: Tomi Jylhä-Ollila, Finland 2015
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#ifndef K_CHORUS_STATE_H
#define K_CHORUS_STATE_H


#include <Decl.h>
#include <player/devices/Device_state.h>
#include <player/devices/Proc_state.h>
#include <string/key_pattern.h>

#include <stdbool.h>
#include <stdint.h>


Device_state* new_Chorus_pstate(
        const Device* device, int32_t audio_rate, int32_t audio_buffer_size);

bool Chorus_pstate_set_voice_delay(
        Device_state* dstate, const Key_indices indices, double value);
bool Chorus_pstate_set_voice_range(
        Device_state* dstate, const Key_indices indices, double value);
bool Chorus_pstate_set_voice_speed(
        Device_state* dstate, const Key_indices indices, double value);
bool Chorus_pstate_set_voice_volume(
        Device_state* dstate, const Key_indices indices, double value);

Proc_state_get_cv_float_controls_mut_func Chorus_pstate_get_cv_delay_variance;
Proc_state_get_cv_float_controls_mut_func Chorus_pstate_get_cv_volume;


#endif // K_CHORUS_STATE_H


