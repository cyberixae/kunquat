

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
#include <limits.h>
#include <stdbool.h>

#include <Active_names.h>
#include <Event_common.h>
#include <Event_generator_set_reltime.h>
#include <File_base.h>
#include <Generator.h>
#include <kunquat/limits.h>
#include <string_common.h>
#include <Value.h>
#include <xassert.h>
#include <xmemory.h>


#if 0
static Event_field_desc set_reltime_desc[] =
{
    {
        .type = EVENT_FIELD_RELTIME,
        .min.field.Reltime_type = { INT64_MIN, 0 },
        .max.field.Reltime_type = { INT64_MAX, KQT_RELTIME_BEAT - 1 }
    },
    {
        .type = EVENT_FIELD_NONE
    }
};
#endif


Event_create_constructor(Event_generator,
                         EVENT_GENERATOR_SET_RELTIME,
                         set_reltime);


bool Event_generator_set_reltime_process(Generator* gen,
                                         Channel_state* ch_state,
                                         Value* value)
{
    assert(gen != NULL);
    assert(ch_state != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_TIMESTAMP)
    {
        return false;
    }
    char* key = Active_names_get(ch_state->parent.active_names,
                                 ACTIVE_CAT_GEN,
                                 ACTIVE_TYPE_TIMESTAMP);
    if (!string_has_suffix(key, ".jsont"))
    {
        return true;
    }
    return Device_params_modify_value(gen->conf->params, key,
                                      &value->value.Timestamp_type);
}


