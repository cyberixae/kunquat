

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010
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
#include <float.h>

#include <Event_common.h>
#include <Event_global_set_scale_offset.h>
#include <Value.h>
#include <xassert.h>
#include <xmemory.h>


#if 0
static Event_field_desc set_scale_offset_desc[] =
{
    {
        .type = EVENT_FIELD_DOUBLE,
        .min.field.double_type = -DBL_MAX,
        .max.field.double_type = DBL_MAX
    },
    {
        .type = EVENT_FIELD_NONE
    }
};
#endif


Event_create_constructor(Event_global,
                         EVENT_GLOBAL_SET_SCALE_OFFSET,
                         set_scale_offset);


bool Event_global_set_scale_offset_process(Playdata* global_state,
                                           Value* value)
{
    assert(global_state != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_FLOAT)
    {
        return false;
    }
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
}


