

/*
 * Author: Tomi Jylhä-Ollila, Finland 2014
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <stdlib.h>

#include <debug/assert.h>
#include <kunquat/events.h>
#include <player/Param_validator.h>
#include <string/common.h>
#include <Value.h>


static const char* event_names[] =
{
#define EVENT_TYPE_DEF(name, category, type_suffix, arg_type, validator) name,
#include <player/Event_types.h>
    NULL
};


const char** kqt_get_event_names(void)
{
    return event_names;
}


const struct
{
    const char* name;
    const Value_type arg_type;
    const Param_validator validator;
} name_to_arg_type[] =
{
#define EVENT_TYPE_DEF(name, category, type_suffix, arg_type, validator) \
    { name, VALUE_TYPE_##arg_type, validator },
#include <player/Event_types.h>
    { NULL, VALUE_TYPE_NONE, NULL }
};


const char* kqt_get_event_arg_type(const char* event_name)
{
    for (int i = 0; name_to_arg_type[i].name != NULL; ++i)
    {
        const char* cur_name = name_to_arg_type[i].name;
        if (string_eq(event_name, cur_name))
        {
            // Special case handling for pitches
            const Param_validator validator = name_to_arg_type[i].validator;
            if (validator == v_pitch)
                return "pitch";

            const Value_type arg_type = name_to_arg_type[i].arg_type;
            switch (arg_type)
            {
                case VALUE_TYPE_NONE:
                    return NULL;

                case VALUE_TYPE_BOOL:
                    return "bool";

                case VALUE_TYPE_INT:
                    return "int";

                case VALUE_TYPE_FLOAT:
                    return "float";

                case VALUE_TYPE_TSTAMP:
                    return "tstamp";

                case VALUE_TYPE_STRING:
                    return "string";

                case VALUE_TYPE_PAT_INST_REF:
                    return "pat";

                default:
                    assert(false);
            }
        }
    }

    return NULL;
}


