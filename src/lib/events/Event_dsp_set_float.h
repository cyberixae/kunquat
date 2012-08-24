

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


#ifndef K_EVENT_DSP_SET_FLOAT_H
#define K_EVENT_DSP_SET_FLOAT_H


#include <Channel_state.h>
#include <DSP_conf.h>
#include <Reltime.h>
#include <Value.h>


bool Event_dsp_set_float_process(DSP_conf* dsp_conf,
                                 Channel_state* ch_state,
                                 Value* value);


#endif // K_EVENT_DSP_SET_FLOAT_H

