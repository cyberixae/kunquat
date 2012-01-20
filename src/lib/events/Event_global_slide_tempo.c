

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


#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>

#include <Event_common.h>
#include <Event_global_slide_tempo.h>
#include <Reltime.h>
#include <Value.h>
#include <xassert.h>
#include <xmemory.h>


static Event_field_desc slide_tempo_desc[] =
{
    {
        .type = EVENT_FIELD_DOUBLE,
        .min.field.double_type = 1,
        .max.field.double_type = 999
    },
    {
        .type = EVENT_FIELD_NONE
    }
};


Event_create_constructor(Event_global,
                         EVENT_GLOBAL_SLIDE_TEMPO,
                         slide_tempo);


bool Event_global_slide_tempo_process(Playdata* global_state, Value* value)
{
    assert(global_state != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_FLOAT)
    {
        return false;
    }
    Reltime_init(&global_state->tempo_slide_int_left);
    Reltime_copy(&global_state->tempo_slide_left,
                 &global_state->tempo_slide_length);
    double rems_total =
            (double)Reltime_get_beats(&global_state->tempo_slide_length) *
                    KQT_RELTIME_BEAT +
                    Reltime_get_rem(&global_state->tempo_slide_length);
    double slices = rems_total / 36756720; // slide updated 24 times per beat
    global_state->tempo_slide_update = (value->value.float_type -
                                        global_state->tempo) / slices;
    global_state->tempo_slide_target = value->value.float_type;
    if (global_state->tempo_slide_update < 0)
    {
        global_state->tempo_slide = -1;
    }
    else if (global_state->tempo_slide_update > 0)
    {
        global_state->tempo_slide = 1;
    }
    else
    {
        global_state->tempo_slide = 0;
        global_state->tempo = value->value.float_type;
    }
    return true;
}


