

/*
 * Author: Tomi Jylhä-Ollila, Finland 2016
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#ifndef K_PROC_PANNING_H
#define K_PROC_PANNING_H


#include <init/devices/Device_impl.h>


typedef struct Proc_panning
{
    Device_impl parent;
    double panning;
} Proc_panning;


/**
 * Create a new panning processor.
 *
 * \return   The new panning processor if successful, or \c NULL if memory
 *           allocation failed.
 */
Device_impl* new_Proc_panning(void);


#endif // K_PROC_PANNING_H

