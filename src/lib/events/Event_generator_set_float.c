

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
#include <assert.h>
#include <stdbool.h>

#include <Event_common.h>
#include <Event_generator_set_float.h>
#include <File_base.h>
#include <Generator.h>
#include <string_common.h>

#include <xmemory.h>


static Event_field_desc set_float_desc[] =
{
    {
        .type = EVENT_FIELD_STRING
    },
    {
        .type = EVENT_FIELD_DOUBLE,
        .min.field.double_type = -INFINITY,
        .max.field.double_type = INFINITY
    },
    {
        .type = EVENT_FIELD_NONE
    }
};


static bool Event_generator_set_float_set(Event* event, int index, void* data);


static void* Event_generator_set_float_get(Event* event, int index);


Event_create_constructor(Event_generator_set_float,
                         EVENT_GENERATOR_SET_FLOAT,
                         set_float_desc,
                         event->value = 0);


static bool Event_generator_set_float_set(Event* event, int index, void* data)
{
    assert(event != NULL);
    assert(event->type == EVENT_GENERATOR_SET_FLOAT);
    Event_generator_set_float* set_float = (Event_generator_set_float*)event;
    if (index == 1)
    {
        assert(data != NULL);
        set_float->value = *(double*)data;
        return true;
    }
    return false;
}


static void* Event_generator_set_float_get(Event* event, int index)
{
    assert(event != NULL);
    assert(event->type == EVENT_GENERATOR_SET_FLOAT);
    Event_generator_set_float* set_float = (Event_generator_set_float*)event;
    if (index == 1)
    {
        return &set_float->value;
    }
    return NULL;
}


bool Event_generator_set_float_process(Generator* gen, char* fields)
{
    assert(gen != NULL);
    if (fields == NULL)
    {
        return false;
    }
    Read_state* state = READ_STATE_AUTO;
    fields = read_const_char(fields, '[', state);
    char key[100] = { '\0' };
    fields = read_string(fields, key, 99, state);
    fields = read_const_char(fields, ',', state);
    if (state->error || !string_has_suffix(key, ".jsonf"))
    {
        return false;
    }
    return Generator_params_modify_value(gen->type_params, key, fields);
}

