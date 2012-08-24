

/*
 * Author: Tomi Jylhä-Ollila, Finland 2011
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <stdlib.h>

#include <Effect.h>
#include <Effect_table.h>
#include <Etable.h>
#include <xassert.h>
#include <xmemory.h>


struct Effect_table
{
    int size;
    Etable* effects;
};


Effect_table* new_Effect_table(int size)
{
    assert(size > 0);
    Effect_table* table = xalloc(Effect_table);
    if (table == NULL)
    {
        return NULL;
    }
    table->effects = NULL;
    table->effects = new_Etable(size, (void (*)(void*))del_Effect);
    if (table->effects == NULL)
    {
        del_Effect_table(table);
        return NULL;
    }
    table->size = size;
    return table;
}


bool Effect_table_set(Effect_table* table, int index, Effect* eff)
{
    assert(table != NULL);
    assert(index >= 0);
    assert(index < table->size);
    assert(eff != NULL);
    return Etable_set(table->effects, index, eff);
}


Effect* Effect_table_get(Effect_table* table, int index)
{
    assert(table != NULL);
    assert(index >= 0);
    assert(index < table->size);
    return Etable_get(table->effects, index);
}


void Effect_table_remove(Effect_table* table, int index)
{
    assert(table != NULL);
    assert(index >= 0);
    assert(index < table->size);
    Etable_remove(table->effects, index);
    return;
}


void Effect_table_clear(Effect_table* table)
{
    assert(table != NULL);
    Etable_clear(table->effects);
    return;
}


void del_Effect_table(Effect_table* table)
{
    if (table == NULL)
    {
        return;
    }
    del_Etable(table->effects);
    xfree(table);
    return;
}

