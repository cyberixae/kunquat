

/*
 * Author: Tomi Jylhä-Ollila, Finland 2010-2013
 *
 * This file is part of Kunquat.
 *
 * CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
 *
 * To the extent possible under law, Kunquat Affirmers have waived all
 * copyright and related or neighboring rights to Kunquat.
 */


#include <stdlib.h>

#include <Device_params.h>
#include <DSP.h>
#include <DSP_conf.h>
#include <memory.h>
#include <string_common.h>
#include <xassert.h>


DSP_conf* new_DSP_conf(void)
{
    DSP_conf* conf = memory_alloc_item(DSP_conf);
    if (conf == NULL)
    {
        return NULL;
    }
    conf->params = NULL;
    conf->params = new_Device_params();
    if (conf->params == NULL)
    {
        del_DSP_conf(conf);
        return NULL;
    }
    return conf;
}


bool DSP_conf_parse(DSP_conf* conf,
                    const char* key,
                    void* data,
                    long length,
                    Device* device,
                    Read_state* state)
{
    assert(conf != NULL);
    assert(key != NULL);
    assert((data == NULL) == (length == 0));
    assert(length >= 0);
    assert(state != NULL);
    (void)device;
    if (state->error)
    {
        return false;
    }
#if 0
    if ((string_has_prefix(key, "i/") || string_has_prefix(key, "c/")) &&
            key_is_device_param(key))
    {
        if (device != NULL)
        {
            DSP_set_conf((DSP*)device, conf);
        }
        if (!Device_params_parse_value(conf->params, key,
                                       data, length,
                                       state))
        {
            return false;
        }
        if (device != NULL)
        {
            return Device_update_key(device, key + 2);
        }
        return true;
    }
#endif
    return true;
}


void del_DSP_conf(DSP_conf* conf)
{
    if (conf == NULL)
    {
        return;
    }
    del_Device_params(conf->params);
    memory_free(conf);
    return;
}


