

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

#include <containers/Etable.h>
#include <debug/assert.h>
#include <devices/Instrument.h>
#include <memory.h>
#include <module/Ins_table.h>


struct Ins_table
{
    int size;
    Etable* insts;
};


Ins_table* new_Ins_table(int size)
{
    assert(size > 0);

    Ins_table* table = memory_alloc_item(Ins_table);
    if (table == NULL)
        return NULL;

    table->insts = new_Etable(size, (void (*)(void*))del_Instrument);
    if (table->insts == NULL)
    {
        memory_free(table);
        return NULL;
    }

    table->size = size;

    return table;
}


bool Ins_table_set(Ins_table* table, int index, Instrument* ins)
{
    assert(table != NULL);
    assert(index >= 0);
    assert(index < table->size);
    assert(ins != NULL);

    return Etable_set(table->insts, index, ins);
}


Instrument* Ins_table_get(Ins_table* table, int index)
{
    assert(table != NULL);
    assert(index >= 0);
    assert(index < table->size);

    return Etable_get(table->insts, index);
}


void Ins_table_remove(Ins_table* table, int index)
{
    assert(table != NULL);
    assert(index >= 0);
    assert(index < table->size);

    Etable_remove(table->insts, index);

    return;
}


void Ins_table_clear(Ins_table* table)
{
    assert(table != NULL);
    Etable_clear(table->insts);
    return;
}


void del_Ins_table(Ins_table* table)
{
    if (table == NULL)
        return;

    del_Etable(table->insts);
    memory_free(table);

    return;
}


