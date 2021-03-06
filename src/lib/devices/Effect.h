

/*
 * Author: Tomi Jylhä-Ollila, Finland 2011-2014
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#ifndef K_EFFECT_H
#define K_EFFECT_H


#include <stdbool.h>
#include <stdint.h>

#include <Decl.h>
#include <devices/Device.h>
#include <devices/DSP_table.h>


typedef struct Effect Effect;


/**
 * Create a new Effect.
 *
 * \return   The new Effect if successful, or \c NULL if memory allocation
 *           failed.
 */
Effect* new_Effect(void);


/**
 * Parse an Effect header from a textual description.
 *
 * \param eff     The Effect -- must not be \c NULL.
 * \param str     The textual description.
 * \param state   The Read state -- must not be \c NULL.
 *
 * \return   \c true if successful, otherwise \c false.
 */
//bool Effect_parse_header(Effect* eff, char* str, Read_state* state);


/**
 * Get a DSP of the Effect.
 *
 * \param eff     The Effect -- must not be \c NULL.
 * \param index   The index of the DSP -- must be >= \c 0 and
 *                < \c KQT_DSPS_MAX.
 *
 * \return   The DSP if one exists, otherwise \c NULL.
 */
const DSP* Effect_get_dsp(const Effect* eff, int index);


/**
 * Get the DSP table of the Effect.
 *
 * \param eff   The Effect -- must not be \c NULL.
 *
 * \return   The DSP table.
 */
const DSP_table* Effect_get_dsps(const Effect* eff);


/**
 * Get the mutable DSP table of the Effect.
 *
 * \param eff   The Effect -- must not be \c NULL.
 *
 * \return   The DSP table.
 */
DSP_table* Effect_get_dsps_mut(Effect* eff);


/**
 * Set the Connections of the Effect.
 *
 * Previously set Connections will be removed if found.
 *
 * \param eff     The Effect -- must not be \c NULL.
 * \param graph   The Connections, or \c NULL.
 */
void Effect_set_connections(Effect* eff, Connections* graph);


/**
 * Prepare the Connections of the Effect.
 *
 * This function assumes that the outer input and output buffers of the Effect
 * have been allocated.
 *
 * \param eff      The Effect -- must not be \c NULL.
 * \param states   The Device states -- must not be \c NULL.
 *
 * \return   \c true if successful, or \c false if memory allocation failed.
 */
bool Effect_prepare_connections(const Effect* eff, Device_states* states);


/**
 * Get the input interface of the Effect.
 *
 * \param eff   The Effect -- must not be \c NULL.
 *
 * \return   The input interface.
 */
const Device* Effect_get_input_interface(const Effect* eff);


/**
 * Get the output interface of the Effect.
 *
 * \param eff   The Effect -- must not be \c NULL.
 *
 * \return   The output interface.
 */
const Device* Effect_get_output_interface(const Effect* eff);


/**
 * Destroy an existing Effect.
 *
 * \param eff   The Effect, or \c NULL.
 */
void del_Effect(Effect* eff);


#endif // K_EFFECT_H


