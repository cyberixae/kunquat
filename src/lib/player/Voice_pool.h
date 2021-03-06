

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


#ifndef K_VOICE_POOL_H
#define K_VOICE_POOL_H


#include <stdint.h>
#include <stdbool.h>

#include <player/Voice.h>


/**
 * Voice pool manages the allocation of Voices.
 */
typedef struct Voice_pool
{
    uint16_t size;
    uint8_t events;
    size_t state_size;
    Voice** voices;
} Voice_pool;


/**
 * Create a new Voice pool.
 *
 * \param size   The number of Voices in the Voice pool -- must be >= \c 0.
 *
 * \return   The new Voice pool if successful, or \c NULL if memory allocation
 *           failed.
 */
Voice_pool* new_Voice_pool(uint16_t size);


/**
 * Reserve space for the Voice states.
 *
 * \param pool         The Voice pool -- must not be \c NULL.
 * \param state_size   The amount of bytes to reserve for the Voice states.
 *
 * \return   \c true if successful, or \c false if memory allocation failed.
 */
bool Voice_pool_reserve_state_space(Voice_pool* pool, size_t state_size);


/**
 * Change the amount of Voices in the Voice pool.
 *
 * \param pool   The Voice pool -- must not be \c NULL.
 * \param size   The new size -- must be > \c 0.
 *
 * \return   \c true if resizing succeeded, or \c false if memory allocation
 *           failed. Note that decreasing the number of Voices may still have
 *           occurred even if the operation fails.
 */
bool Voice_pool_resize(Voice_pool* pool, uint16_t size);


/**
 * Get the amount of Voices in the Voice pool.
 *
 * \param pool   The Voice pool -- must not be \c NULL.
 *
 * \return   The number of Voices.
 */
uint16_t Voice_pool_get_size(const Voice_pool* pool);


/**
 * Get a Voice from the Voice pool.
 *
 * In case all the Voices are in use, the Voice considered least important is
 * reinitialised and returned.
 *
 * If the caller gives an existing Voice as a parameter, no new Voice will be
 * returned. Instead, the Voice pool will check whether this Voice has the
 * same ID as the caller provides (if yes, the caller is still allowed to use
 * this Voice and the \a voice parameter itself will be returned; otherwise
 * \c NULL).
 *
 * \param pool      The Voice pool -- must not be \c NULL.
 * \param voice     An existing Voice. If \c NULL is returned, the caller must
 *                  not access this Voice.
 * \param id        An identification number for an existing Voice that needs
 *                  to be matched.
 *
 * \return   The Voice reserved for use, or \c NULL if \a voice is no longer
 *           under the control of the caller or the pool size is \c 0.
 */
Voice* Voice_pool_get_voice(Voice_pool* pool, Voice* voice, uint64_t id);


/**
 * Prepare the Voice pool for a new mixing cycle.
 *
 * \param pool   The Voice pool -- must not be \c NULL.
 */
void Voice_pool_prepare(Voice_pool* pool);


/**
 * Mix the background Voices in the Voice pool.
 *
 * \param pool     The Voice pool -- must not be \c NULL.
 * \param states   The Device states -- must not be \c NULL.
 * \param amount   The number of frames to be mixed.
 * \param offset   The buffer offset.
 * \param freq     The mixing frequency -- must be > \c 0.
 *
 * \return   The number of active Voices.
 */
uint16_t Voice_pool_mix_bg(
        Voice_pool* pool,
        Device_states* states,
        uint32_t amount,
        uint32_t offset,
        uint32_t freq,
        double tempo);


/**
 * Reset all Voices in the Voice pool.
 *
 * \param pool   The Voice pool -- must not be \c NULL.
 */
void Voice_pool_reset(Voice_pool* pool);


/**
 * Destroy an existing Voice pool.
 *
 * \param pool   The Voice pool, or \c NULL.
 */
void del_Voice_pool(Voice_pool* pool);


#endif // K_VOICE_POOL_H


