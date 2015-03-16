

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010-2015
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <stdlib.h>
#include <stdbool.h>

#include <debug/assert.h>
#include <player/events/Event_common.h>
#include <player/events/Event_ins_decl.h>
#include <Value.h>


bool Event_ins_set_sustain_process(
        const Instrument* ins,
        const Instrument_params* ins_params,
        Ins_state* ins_state,
        Device_states* dstates,
        const Value* value)
{
    assert(ins != NULL);
    assert(ins_params != NULL);
    assert(ins_state != NULL);
    assert(dstates != NULL);
    assert(value != NULL);
    assert(value->type == VALUE_TYPE_FLOAT);
    (void)ins;
    (void)ins_params;
    (void)dstates;

    ins_state->sustain = value->value.float_type;

    return true;
}


