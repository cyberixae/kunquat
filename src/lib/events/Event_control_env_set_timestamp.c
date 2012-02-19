

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


#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>

#include <Active_names.h>
#include <Env_var.h>
#include <Environment.h>
#include <Event.h>
#include <Event_common.h>
#include <Event_control.h>
#include <Event_control_env_set_timestamp.h>
#include <Event_type.h>
#include <File_base.h>
#include <General_state.h>
#include <kunquat/limits.h>
#include <Reltime.h>
#include <Value.h>
#include <xassert.h>


#if 0
static Event_field_desc env_set_timestamp_desc[] =
{
    {
        .type = EVENT_FIELD_STRING
    },
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


Event_create_constructor(Event_control,
                         EVENT_CONTROL_ENV_SET_TIMESTAMP,
                         env_set_timestamp);


bool Event_control_env_set_timestamp_process(General_state* gstate,
                                             Value* value)
{
    assert(gstate != NULL);
    assert(value != NULL);
    if (value->type != VALUE_TYPE_TIMESTAMP || !gstate->global)
    {
        return false;
    }
    Env_var* var = Environment_get(gstate->env,
                        Active_names_get(gstate->active_names,
                                         ACTIVE_CAT_ENV,
                                         ACTIVE_TYPE_FLOAT));
    if (var == NULL || Env_var_get_type(var) != ENV_VAR_RELTIME)
    {
        return true;
    }
    Env_var_modify_value(var, &value->value.Timestamp_type);
    return true;
}


