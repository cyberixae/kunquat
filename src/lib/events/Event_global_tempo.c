

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010-2013
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

#include <Event_common.h>
#include <Event_master_decl.h>
#include <kunquat/limits.h>
#include <Tstamp.h>
#include <Value.h>
#include <xassert.h>


bool Event_global_set_tempo_process(Master_params* master_params, Playdata* global_state, Value* value)
{
    assert(master_params != NULL || global_state != NULL);
    assert(value != NULL);

    if (master_params != NULL)
    {
        assert(value->type == VALUE_TYPE_FLOAT);
        master_params->tempo_settings_changed = true;
        master_params->tempo = value->value.float_type;
        master_params->tempo_slide = 0;
        return true;
    }

    if (value->type != VALUE_TYPE_FLOAT)
    {
        return false;
    }

    global_state->tempo = value->value.float_type;
    global_state->tempo_slide = 0;

    return true;
}


static void set_tempo_slide_update(Master_params* master_params)
{
    assert(master_params != NULL);

    const double rems_total =
            (double)Tstamp_get_beats(&master_params->tempo_slide_length) *
            KQT_TSTAMP_BEAT +
            Tstamp_get_rem(&master_params->tempo_slide_length);
    double slices = rems_total / KQT_TEMPO_SLIDE_SLICE_LEN;
    master_params->tempo_slide_update =
        (master_params->tempo_slide_target - master_params->tempo) / slices;

    return;
}


bool Event_global_slide_tempo_process(Master_params* master_params, Playdata* global_state, Value* value)
{
    assert(master_params != NULL || global_state != NULL);
    assert(value != NULL);

    if (master_params != NULL)
    {
        assert(value->type == VALUE_TYPE_FLOAT);

        master_params->tempo_settings_changed = true;

        Tstamp_init(&master_params->tempo_slide_slice_left);
        Tstamp_copy(
                &master_params->tempo_slide_left,
                &master_params->tempo_slide_length);
        master_params->tempo_slide_target = value->value.float_type;

        set_tempo_slide_update(master_params);

        if (master_params->tempo_slide_update < 0)
            master_params->tempo_slide = -1;
        else if (master_params->tempo_slide_update > 0)
            master_params->tempo_slide = 1;
        else
        {
            master_params->tempo_slide = 0;
            master_params->tempo = master_params->tempo_slide_target;
        }

        return true;
    }

    if (value->type != VALUE_TYPE_FLOAT)
    {
        return false;
    }

    Tstamp_init(&global_state->tempo_slide_int_left);
    Tstamp_copy(&global_state->tempo_slide_left,
                 &global_state->tempo_slide_length);
    double rems_total =
            (double)Tstamp_get_beats(&global_state->tempo_slide_length) *
                    KQT_TSTAMP_BEAT +
                    Tstamp_get_rem(&global_state->tempo_slide_length);
    double slices = rems_total / KQT_TEMPO_SLIDE_SLICE_LEN;
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


bool Event_global_slide_tempo_length_process(
        Master_params* master_params,
        Playdata* global_state,
        Value* value)
{
    assert(master_params != NULL || global_state != NULL);
    assert(value != NULL);

    if (master_params != NULL)
    {
        assert(value->type == VALUE_TYPE_TSTAMP);

        master_params->tempo_settings_changed = true;

        Tstamp_copy(
                &master_params->tempo_slide_length,
                &value->value.Tstamp_type);

        if (master_params->tempo_slide != 0)
        {
            Tstamp_init(&master_params->tempo_slide_slice_left);
            Tstamp_copy(
                    &master_params->tempo_slide_left,
                    &master_params->tempo_slide_length);

            set_tempo_slide_update(master_params);
        }

        return true;
    }

    if (value->type != VALUE_TYPE_TSTAMP)
    {
        return false;
    }

    if (global_state->tempo_slide != 0)
    {
        Tstamp_init(&global_state->tempo_slide_int_left);
        Tstamp_copy(&global_state->tempo_slide_left,
                     &value->value.Tstamp_type);
        double rems_total =
                (double)Tstamp_get_beats(&value->value.Tstamp_type) *
                KQT_TSTAMP_BEAT +
                Tstamp_get_rem(&value->value.Tstamp_type);
        double slices = rems_total / KQT_TEMPO_SLIDE_SLICE_LEN;
        global_state->tempo_slide_update = (global_state->tempo_slide_target -
                                            global_state->tempo) / slices;
    }

    Tstamp_copy(
            &global_state->tempo_slide_length,
            &value->value.Tstamp_type);

    return true;
}

