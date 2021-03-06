

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


#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>
#include <math.h>

#include <debug/assert.h>
#include <kunquat/limits.h>
#include <Pat_inst_ref.h>
#include <player/Param_validator.h>
#include <string/Streader.h>


#define init_c_streader(param) \
    Streader_init(STREADER_AUTO, (param), strlen((param)))


bool v_any_bool(const char* param)
{
    assert(param != NULL);
    Streader* sr = init_c_streader(param);
    return Streader_read_bool(sr, NULL);
}


bool v_any_int(const char* param)
{
    assert(param != NULL);
    Streader* sr = init_c_streader(param);
    return Streader_read_int(sr, NULL);
}


bool v_any_float(const char* param)
{
    assert(param != NULL);
    Streader* sr = init_c_streader(param);
    return Streader_read_float(sr, NULL);
}


bool v_any_str(const char* param)
{
    assert(param != NULL);
    Streader* sr = init_c_streader(param);
    return Streader_read_string(sr, 0, NULL);
}


bool v_any_ts(const char* param)
{
    assert(param != NULL);
    Streader* sr = init_c_streader(param);
    return Streader_read_tstamp(sr, NULL);
}


bool v_arp_index(const char* param)
{
    assert(param != NULL);

    int64_t index = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &index) &&
        index >= 0 &&
        index < KQT_ARPEGGIO_NOTES_MAX;
}


bool v_arp_speed(const char* param)
{
    assert(param != NULL);

    double speed = NAN;
    Streader* sr = init_c_streader(param);

    return Streader_read_float(sr, &speed) && speed > 0;
}


bool v_cond(const char* param)
{
    assert(param != NULL);
    Streader* sr = init_c_streader(param);
    return Streader_read_string(sr, 0, NULL);
}


bool v_counter(const char* param)
{
    assert(param != NULL);

    int64_t counter = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &counter) &&
        counter >= 0 &&
        counter < 65535;
}


bool v_dsp(const char* param)
{
    assert(param != NULL);

    int64_t dsp = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &dsp) && (dsp >= 0) && (dsp < KQT_DSPS_MAX);
}


bool v_effect(const char* param)
{
    assert(param != NULL);

    int64_t effect = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &effect) &&
        effect >= 0 &&
        effect < KQT_EFFECTS_MAX;
}


bool v_finite_float(const char* param)
{
    assert(param != NULL);

    double value = NAN;
    Streader* sr = init_c_streader(param);

    return Streader_read_float(sr, &value) && isfinite(value);
}


bool v_force(const char* param)
{
    assert(param != NULL);

    double force = NAN;
    Streader* sr = init_c_streader(param);

    return Streader_read_float(sr, &force) && (force <= 18);
}


bool v_gen(const char* param)
{
    assert(param != NULL);

    int64_t gen = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &gen) &&
        gen >= 0 &&
        gen < KQT_GENERATORS_MAX;
}


bool v_hit(const char* param)
{
    assert(param != NULL);

    int64_t hit = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &hit) && (hit >= 0) && (hit < KQT_HITS_MAX);
}


bool v_ins(const char* param)
{
    assert(param != NULL);

    int64_t ins = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &ins) &&
        ins >= 0 &&
        ins < KQT_INSTRUMENTS_MAX;
}


bool v_key(const char* param)
{
    assert(param != NULL);

    char key[KQT_KEY_LENGTH_MAX + 1] = "";
    Streader* sr = init_c_streader(param);

    if (!Streader_read_string(sr, KQT_KEY_LENGTH_MAX + 1, key))
        return false;

    int len = strlen(key);
    if (len == 0 || len > KQT_KEY_LENGTH_MAX)
        return false;

    for (int i = 0; i < len; ++i)
    {
        if (!isalpha(key[i]) && strchr("_./", key[i]) == NULL)
            return false;
    }

    return true;
}


bool v_lowpass(const char* param)
{
    assert(param != NULL);
    return v_finite_float(param); // TODO
}


bool v_nonneg_float(const char* param)
{
    assert(param != NULL);

    double value = NAN;
    Streader* sr = init_c_streader(param);

    return Streader_read_float(sr, &value) && (value >= 0);
}


bool v_nonneg_ts(const char* param)
{
    assert(param != NULL);

    Tstamp* ts = TSTAMP_AUTO;
    Streader* sr = init_c_streader(param);

    return Streader_read_tstamp(sr, ts) &&
        Tstamp_cmp(ts, Tstamp_set(TSTAMP_AUTO, 0, 0)) >= 0;
}


bool v_note_entry(const char* param)
{
    assert(param != NULL);

    int64_t ne = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &ne) && (ne >= 0) && (ne < KQT_SCALE_NOTES);
}


bool v_panning(const char* param)
{
    assert(param != NULL);

    double pan = NAN;
    Streader* sr = init_c_streader(param);

    return Streader_read_float(sr, &pan) && (pan >= -1) && (pan <= 1);
}


bool v_pattern(const char* param)
{
    assert(param != NULL);

    int64_t pat = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &pat) && (pat >= 0) && (pat < KQT_PATTERNS_MAX);
}


bool v_piref(const char* param)
{
    assert(param != NULL);
    Streader* sr = init_c_streader(param);
    return Streader_read_piref(sr, NULL);
}


bool v_pitch(const char* param)
{
    assert(param != NULL);
    return v_finite_float(param);
}


bool v_resonance(const char* param)
{
    assert(param != NULL);

    double res = NAN;
    Streader* sr = init_c_streader(param);

    return Streader_read_float(sr, &res) && (res >= 0) && (res <= 99);
}


bool v_scale(const char* param)
{
    assert(param != NULL);

    int64_t scale = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &scale) &&
        scale >= 0 &&
        scale < KQT_SCALES_MAX;
}


bool v_song(const char* param)
{
    assert(param != NULL);

    int64_t song = -2;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &song) &&
        song >= -1 &&
        song < KQT_SONGS_MAX;
}


bool v_system(const char* param)
{
    assert(param != NULL);

    int64_t system = -1;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &system) && (system >= -1);
}


bool v_sustain(const char* param)
{
    assert(param != NULL);

    double sustain = NAN;
    Streader* sr = init_c_streader(param);

    return Streader_read_float(sr, &sustain) &&
        sustain >= 0 &&
        sustain <= 1;
}


bool v_tempo(const char* param)
{
    assert(param != NULL);

    double tempo = NAN;
    Streader* sr = init_c_streader(param);

    return Streader_read_float(sr, &tempo) && (tempo >= 1) && (tempo <= 999);
}


bool v_track(const char* param)
{
    assert(param != NULL);

    int64_t track = -2;
    Streader* sr = init_c_streader(param);

    return Streader_read_int(sr, &track) &&
        track >= -1 &&
        track < KQT_TRACKS_MAX;
}


bool v_tremolo_depth(const char* param)
{
    assert(param != NULL);

    double depth = NAN;
    Streader* sr = init_c_streader(param);

    return Streader_read_float(sr, &depth) && (depth >= 0) && (depth <= 24);
}


bool v_volume(const char* param)
{
    assert(param != NULL);

    double vol = NAN;
    Streader* sr = init_c_streader(param);

    return Streader_read_float(sr, &vol) && (vol <= 0);
}


#undef init_c_streader


