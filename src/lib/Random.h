

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010-2011
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#ifndef K_RANDOM_H
#define K_RANDOM_H


#include <stdlib.h>
#include <stdint.h>


/**
 * This is a portable pseudo-random generator.
 */
typedef struct Random Random;


/**
 * The maximum 32-bit number generated by the pseudo-random generator.
 */
#define KQT_RANDOM32_MAX UINT32_MAX


/**
 * The maximum 64-bit number generated by the pseudo-random generator.
 */
#define KQT_RANDOM64_MAX UINT64_MAX


/**
 * The maximum length of a random context description string.
 */
#define CONTEXT_LEN_MAX 15


/**
 * Creates a new Random generator.
 *
 * \return   The new Random if successful, or \c NULL if memory allocation
 *           failed.
 */
Random* new_Random(void);


/**
 * Sets the context of the Random.
 *
 * The new context description becomes active at the next call of
 * Random_set_seed.
 *
 * \param random    The Random generator -- must not be \c NULL.
 * \param context   The context description -- must not be \c NULL or longer
 *                  than \c CONTEXT_LEN_MAX bytes (excluding the null
 *                  terminator).
 */
void Random_set_context(Random* random, char* context);


/**
 * Sets the random seed in the Random.
 *
 * \param random   The Random generator -- must not be \c NULL.
 * \param seed     The random seed.
 */
void Random_set_seed(Random* random, uint64_t seed);


/**
 * Restarts the random sequence in the Random.
 *
 * \param random   The Random generator -- must not be \c NULL.
 */
void Random_reset(Random* random);


/**
 * Gets a 32-bit integer from the Random generator.
 *
 * This function returns the 32 most significant bits of the 64-bit
 * state and thus have higher overall quality.
 *
 * \param random   The Random generator -- must not be \c NULL.
 *
 * \return   A pseudorandom integer in the range [0, KQT_RANDOM32_MAX].
 */
uint32_t Random_get_uint32(Random* random);


/**
 * Gets a 64-bit integer from the Random generator.
 *
 * This function is generally not recommended unless a large number of
 * random bits is needed.
 *
 * \param random   The Random generator -- must not be \c NULL.
 *
 * \return   A pseudorandom integer in the range [0, KQT_RANDOM64_MAX].
 */
uint64_t Random_get_uint64(Random* random);


/**
 * Gets an array index.
 *
 * \param random   The Random generator -- must not be \c NULL.
 * \param size     The array size -- must be > \c 0.
 *
 * \return   A pseudorandom integer in the range [0, \a size).
 */
int32_t Random_get_index(Random* random, int32_t size);


/**
 * Gets a floating point number in the range [0, 1.0].
 *
 * This function is not suitable for converting to integers because it may
 * return exactly 1.0 as a result.
 *
 * \param random   The Random generator -- must not be \c NULL.
 *
 * \return   A pseudorandom floating-point number in the range [0, 1.0].
 */
double Random_get_float_scale(Random* random);


/**
 * Gets a floating point number in the range [-1.0, 1.0].
 *
 * \param random   The Random generator -- must not be \c NULL.
 *
 * \return   A pseudorandom floating-point number in the range [-1.0, 1.0].
 */
double Random_get_float_signal(Random* random);


/**
 * Destroys an existing Random generator.
 *
 * \param random   The Random generator, or \c NULL.
 */
void del_Random(Random* random);


#endif // K_RANDOM_H


