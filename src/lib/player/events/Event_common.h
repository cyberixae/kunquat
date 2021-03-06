

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


#ifndef K_EVENT_COMMON_H
#define K_EVENT_COMMON_H


#include <stdbool.h>

#include <Tstamp.h>


#define Event_check_voice(ch_state, gen)                        \
    if (true)                                                   \
    {                                                           \
        if ((ch_state)->fg[(gen)] == NULL)                      \
            continue;                                           \
                                                                \
        (ch_state)->fg[(gen)] =                                 \
                Voice_pool_get_voice((ch_state)->pool,          \
                                     (ch_state)->fg[(gen)],     \
                                     (ch_state)->fg_id[(gen)]); \
        if ((ch_state)->fg[(gen)] == NULL)                      \
            continue;                                           \
    }                                                           \
    else (void)0


#endif // K_EVENT_COMMON_H


