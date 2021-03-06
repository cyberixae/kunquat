

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
#include <stdio.h>

#include <Audio_buffer.h>
#include <debug/assert.h>
#include <kunquat/limits.h>
#include <mathnum/common.h>
#include <memory.h>


struct Audio_buffer
{
    uint32_t size;
    kqt_frame* bufs[KQT_BUFFERS_MAX];
};


Audio_buffer* new_Audio_buffer(uint32_t size)
{
    //assert(size >= 0);
    assert(size <= KQT_AUDIO_BUFFER_SIZE_MAX);

    Audio_buffer* buffer = memory_alloc_item(Audio_buffer);
    if (buffer == NULL)
        return NULL;

    // Sanitise fields
    buffer->size = size;

    for (int i = 0; i < KQT_BUFFERS_MAX; ++i)
        buffer->bufs[i] = NULL;

    // Init buffers
    if (buffer->size > 0)
    {
        for (int i = 0; i < KQT_BUFFERS_MAX; ++i)
        {
            buffer->bufs[i] = memory_alloc_items(kqt_frame, size);
            if (buffer->bufs[i] == NULL)
            {
                //fprintf(stderr, "Calling destroy at %s:%d\n", __FILE__, __LINE__);
                del_Audio_buffer(buffer);
                return NULL;
            }
        }
    }

//    fprintf(stderr, "Created buffer %p with arrays %p and %p\n",
//            (void*)buffer, (void*)buffer->bufs[0], (void*)buffer->bufs[1]);

    Audio_buffer_clear(buffer, 0, size);

    return buffer;
}


uint32_t Audio_buffer_get_size(const Audio_buffer* buffer)
{
    assert(buffer != NULL);
    return buffer->size;
}


bool Audio_buffer_resize(Audio_buffer* buffer, uint32_t size)
{
    assert(buffer != NULL);
    //assert(size >= 0);
    assert(size <= KQT_AUDIO_BUFFER_SIZE_MAX);

    if (buffer->size == size)
        return true;

    // Handle zero size
    if (size == 0)
    {
        for (int i = 0; i < KQT_BUFFERS_MAX; ++i)
        {
            memory_free(buffer->bufs[i]);
            buffer->bufs[i] = NULL;
        }
        buffer->size = size;
        return true;
    }

    // Resize
    for (int i = 0; i < KQT_BUFFERS_MAX; ++i)
    {
        kqt_frame* new_buf = memory_realloc_items(
                kqt_frame,
                size,
                buffer->bufs[i]);
        if (new_buf == NULL)
        {
            buffer->size = min(buffer->size, size);
            return false;
        }
        buffer->bufs[i] = new_buf;
    }
    buffer->size = size;

    return true;
}


void Audio_buffer_clear(Audio_buffer* buffer, uint32_t start, uint32_t until)
{
    assert(buffer != NULL);
    assert(start < buffer->size || buffer->size == 0);
    assert(until <= buffer->size);

//    fprintf(stderr, "Clearing %p [%d..%d)\n",
//            (void*)buffer, (int)start, (int)until);
    for (int i = 0; i < KQT_BUFFERS_MAX; ++i)
    {
        for (uint32_t k = start; k < until; ++k)
            buffer->bufs[i][k] = 0;
    }

    return;
}


void Audio_buffer_mix(
        Audio_buffer* buffer,
        const Audio_buffer* in,
        uint32_t start,
        uint32_t until)
{
    assert(buffer != NULL);
    assert(in != NULL);
    assert(buffer->size == in->size);
    assert(start < buffer->size || buffer->size == 0);
    assert(until <= buffer->size);

    if (buffer == in || until <= start)
    {
//        fprintf(stderr, "Not mixing %p to %p [%d..%d)\n",
//                (void*)in, (void*)buffer, (int)start, (int)until);
        return;
    }

//    fprintf(stderr, "Mixing %p to %p [%d..%d)\n",
//            (void*)in, (void*)buffer, (int)start, (int)until);
    for (int i = 0; i < KQT_BUFFERS_MAX; ++i)
    {
        for (uint32_t k = start; k < until; ++k)
            buffer->bufs[i][k] += in->bufs[i][k];
    }

    return;
}


kqt_frame* Audio_buffer_get_buffer(Audio_buffer* buffer, int index)
{
    assert(buffer != NULL);
    assert(index >= 0);
    assert(index < KQT_BUFFERS_MAX);

    return buffer->bufs[index];
}


void del_Audio_buffer(Audio_buffer* buffer)
{
    if (buffer == NULL)
        return;

    //fprintf(stderr, "Destroying %p\n", (void*)buffer);
    for (int i = 0; i < KQT_BUFFERS_MAX; ++i)
        memory_free(buffer->bufs[i]);

    memory_free(buffer);
    return;
}


