

/*
 * Author: Tomi Jylhä-Ollila, Finland 2013-2014
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <debug/assert.h>
#include <memory.h>
#include <player/Jump_cache.h>
#include <player/Jump_context.h>


struct Jump_cache
{
    AAtree* contexts;

    // Debug checking fields
    size_t num_contexts;
    size_t use_count;
};


static int64_t store_counter = 0;


Jump_cache* new_Jump_cache(size_t num_contexts)
{
    assert(num_contexts > 0);

    Jump_cache* jcache = memory_alloc_item(Jump_cache);
    if (jcache == NULL)
        return NULL;

    jcache->contexts = NULL;
    jcache->num_contexts = 0;
    jcache->use_count = 0;

    jcache->contexts = new_AAtree(
            (int (*)(const void*, const void*))Jump_context_cmp,
            (void (*)(void*))del_Jump_context);
    if (jcache->contexts == NULL)
    {
        del_Jump_cache(jcache);
        return NULL;
    }

    for (size_t i = 0; i < num_contexts; ++i)
    {
        Jump_context* jc = new_Jump_context();
        if (jc == NULL)
        {
            del_Jump_cache(jcache);
            return NULL;
        }

        // Hack: Make sure no contexts compare equal to one another
        jc->order = store_counter;
        ++store_counter;

        if (!AAtree_ins(jcache->contexts, jc))
        {
            del_Jump_context(jc);
            del_Jump_cache(jcache);
            return NULL;
        }

        ++jcache->num_contexts;
    }

    return jcache;
}


AAnode* Jump_cache_acquire_context(Jump_cache* jcache)
{
    assert(jcache != NULL);

    Jump_context* key = JUMP_CONTEXT_AUTO;
    key->piref.pat = -1;
    key->piref.inst = -1;
    Tstamp_set(&key->row, -1, 0);

    const Jump_context* elem = AAtree_get_at_least(jcache->contexts, key);
    if (elem == NULL)
    {
        assert(jcache->use_count == jcache->num_contexts);
        return NULL;
    }

    assert(jcache->use_count < jcache->num_contexts);
    ++jcache->use_count;

    return AAtree_detach(jcache->contexts, elem);
}


void Jump_cache_release_context(Jump_cache* jcache, AAnode* handle)
{
    assert(jcache != NULL);
    assert(handle != NULL);

    Jump_context* jc = AAnode_get_data(handle);
    jc->piref.pat = -1;
    jc->piref.inst = -1;
    Tstamp_set(&jc->row, 0, 0);

    // Hack: Make sure no contexts compare equal to one another
    jc->order = store_counter;
    ++store_counter;

    AAtree_attach(jcache->contexts, handle);

    assert(jcache->use_count > 0);
    --jcache->use_count;

    return;
}


void del_Jump_cache(Jump_cache* jcache)
{
    if (jcache == NULL)
        return;

    assert(jcache->use_count == 0);

    del_AAtree(jcache->contexts);
    memory_free(jcache);

    return;
}


