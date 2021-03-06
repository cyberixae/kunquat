

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


#include <stdlib.h>
#include <stdbool.h>

#include <debug/assert.h>
#include <kunquat/limits.h>
#include <player/events/Event_common.h>
#include <player/events/Event_master_decl.h>
#include <Value.h>


bool Event_master_set_scale_process(Master_params* master_params, const Value* value)
{
    assert(master_params != NULL);
    assert(value != NULL);
    assert(value->type == VALUE_TYPE_INT);
    (void)master_params;
    (void)value;

    return false;

#if 0
    global_state->scale = value->value.int_type;

    return true;
#endif
}


bool Event_master_set_scale_fixed_point_process(
        Master_params* master_params,
        const Value* value)
{
    assert(master_params != NULL);
    assert(value != NULL);
    assert(value->type == VALUE_TYPE_INT);
    (void)master_params;
    (void)value;

    return false;

#if 0
    global_state->scale_fixed_point = value->value.int_type;

    return true;
#endif
}


bool Event_master_set_scale_offset_process(
        Master_params* master_params,
        const Value* value)
{
    assert(master_params != NULL);
    assert(value != NULL);
    assert(value->type == VALUE_TYPE_FLOAT);
    (void)master_params;
    (void)value;

    return false;

#if 0
    if (global_state->scales == NULL)
    {
        return true;
    }
    Scale* scale = global_state->scales[global_state->scale];
    if (scale == NULL)
    {
        return true;
    }
    Scale_set_pitch_offset(scale, value->value.float_type);
    return true;
#endif
}


bool Event_master_mimic_scale_process(
        Master_params* master_params,
        const Value* value)
{
    assert(master_params != NULL);
    assert(value != NULL);
    assert(value->type == VALUE_TYPE_INT);
    (void)master_params;
    (void)value;

    return false;

#if 0
    if (global_state->scales == NULL)
    {
        return true;
    }
    Scale* scale = global_state->scales[global_state->scale];
    Scale* modifier = global_state->scales[value->value.int_type];
    if (scale == NULL || modifier == NULL)
    {
        return true;
    }
    Scale_retune_with_source(scale, modifier);
    return true;
#endif
}


bool Event_master_shift_scale_intervals_process(
        Master_params* master_params,
        const Value* value)
{
    assert(master_params != NULL);
    assert(value != NULL);
    assert(value->type == VALUE_TYPE_INT);
    (void)master_params;
    (void)value;

    return false;

#if 0
    if (global_state->scales == NULL)
    {
        return true;
    }
    Scale* scale = global_state->scales[global_state->scale];
    if (scale == NULL ||
            Scale_get_note_count(scale) <= value->value.int_type ||
            Scale_get_note_count(scale) <= global_state->scale_fixed_point)
    {
        return true;
    }
    Scale_retune(
            scale,
            value->value.int_type,
            global_state->scale_fixed_point);
    return true;
#endif
}


