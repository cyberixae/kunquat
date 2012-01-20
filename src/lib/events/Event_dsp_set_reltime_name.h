

/*
 * Author: Tomi Jylhä-Ollila, Finland 2011-2012
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#ifndef K_EVENT_DSP_SET_RELTIME_NAME_H
#define K_EVENT_DSP_SET_RELTIME_NAME_H


#include <Channel_state.h>
#include <Event_dsp.h>
#include <DSP_conf.h>
#include <Reltime.h>
#include <Value.h>


Event* new_Event_dsp_set_reltime_name(Reltime* pos);


bool Event_dsp_set_reltime_name_process(DSP_conf* dsp_conf,
                                        Channel_state* ch_state,
                                        Value* value);


#endif // K_EVENT_DSP_SET_RELTIME_NAME_H


