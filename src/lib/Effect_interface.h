

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


#ifndef K_EFFECT_INTERFACE_H
#define K_EFFECT_INTERFACE_H


#include <Device.h>


typedef struct Effect_interface
{
    Device parent;
} Effect_interface;


/**
 * Creates a new Effect interface.
 *
 * \param buf_len    The length of a mixing buffer -- must be > \c 0.
 * \param mix_rate   The mixing rate -- must be > \c 0.
 *
 * \return   The new Effect interface if successful, or \c NULL if memory
 *           allocation failed.
 */
Effect_interface* new_Effect_interface(uint32_t buf_len,
                                       uint32_t mix_rate);


/**
 * Destroys an existing Effect interface.
 *
 * \param ei   The Effect interface, or \c NULL.
 */
void del_Effect_interface(Effect_interface* ei);


#endif // K_EFFECT_INTERFACE_H

