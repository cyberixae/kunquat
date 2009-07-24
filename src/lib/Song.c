

/*
 * Copyright 2009 Tomi Jylhä-Ollila
 *
 * This file is part of Kunquat.
 *
 * Kunquat is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Kunquat is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Kunquat.  If not, see <http://www.gnu.org/licenses/>.
 */


#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <math.h>

#include <Real.h>
#include <Song.h>
#include <File_base.h>
#include <File_tree.h>
#include <math_common.h>

#include <xmemory.h>


Song* new_Song(int buf_count, uint32_t buf_size, uint8_t events)
{
    assert(buf_count >= 1);
    assert(buf_count <= KQT_BUFFERS_MAX);
    assert(buf_size > 0);
    Song* song = xalloc(Song);
    if (song == NULL)
    {
        return NULL;
    }
    song->buf_count = buf_count;
    song->buf_size = buf_size;
    song->priv_bufs[0] = NULL;
    song->voice_bufs[0] = NULL;
    song->order = NULL;
    song->pats = NULL;
    song->insts = NULL;
    for (int i = 0; i < KQT_SCALES_MAX; ++i)
    {
        song->notes[i] = NULL;
    }
    song->active_notes = &song->notes[0];
    for (int i = 0; i < KQT_BUFFERS_MAX; ++i)
    {
        song->bufs[i] = NULL;
    }
    for (int i = 0; i < buf_count; ++i)
    {
        song->priv_bufs[i] = xnalloc(kqt_frame, buf_size);
        if (song->priv_bufs[i] == NULL)
        {
            del_Song(song);
            return NULL;
        }
        for (uint32_t k = 0; k < buf_size; ++k)
        {
            song->priv_bufs[i][k] = 0;
        }
        song->bufs[i] = song->priv_bufs[i];
        song->voice_bufs[i] = xnalloc(kqt_frame, buf_size);
        if (song->voice_bufs[i] == NULL)
        {
            del_Song(song);
            return NULL;
        }
    }
    song->order = new_Order();
    if (song->order == NULL)
    {
        del_Song(song);
        return NULL;
    }
    song->pats = new_Pat_table(KQT_PATTERNS_MAX);
    if (song->pats == NULL)
    {
        del_Song(song);
        return NULL;
    }
    song->insts = new_Ins_table(KQT_INSTRUMENTS_MAX);
    if (song->insts == NULL)
    {
        del_Song(song);
        return NULL;
    }
    song->notes[0] = new_Note_table(523.25113060119725,
            Real_init_as_frac(REAL_AUTO, 2, 1));
    if (song->notes[0] == NULL)
    {
        del_Song(song);
        return NULL;
    }
    song->events = new_Event_queue(events);
    if (song->events == NULL)
    {
        del_Song(song);
        return NULL;
    }
    Note_table_set_note(song->notes[0],
            0,
            Real_init_as_frac(REAL_AUTO, 1, 1));
    for (int i = 1; i < 12; ++i)
    {
        Note_table_set_note_cents(song->notes[0],
                i,
                i * 100);
    }
    song->mix_vol_dB = -8;
    song->mix_vol = exp2(song->mix_vol_dB / 6);
    song->init_subsong = 0;
    return song;
}


bool Song_read(Song* song, File_tree* tree, Read_state* state)
{
    assert(song != NULL);
    assert(tree != NULL);
    assert(state != NULL);
    if (state->error)
    {
        return false;
    }
    Read_state_init(state, File_tree_get_path(tree));
    if (!File_tree_is_dir(tree))
    {
        Read_state_set_error(state, "Song is not a directory");
        return false;
    }
    char* name = File_tree_get_name(tree);
    if (strncmp(name, MAGIC_ID, strlen(MAGIC_ID)) != 0)
    {
        Read_state_set_error(state, "Directory is not a Kunquat file");
        return false;
    }
    if (name[strlen(MAGIC_ID)] != 'c')
    {
        Read_state_set_error(state, "Directory is not a composition file");
        return false;
    }
    const char* version = "00";
    if (strcmp(name + strlen(MAGIC_ID) + 1, version) != 0)
    {
        Read_state_set_error(state, "Unsupported composition version");
        return false;
    }
    File_tree* info_tree = File_tree_get_child(tree, "composition.json");
    if (info_tree != NULL)
    {
        Read_state_init(state, File_tree_get_path(info_tree));
        if (File_tree_is_dir(info_tree))
        {
            Read_state_set_error(state, "Composition info is a directory");
            return false;
        }
        char* str = File_tree_get_data(info_tree);
        str = read_const_char(str, '{', state);
        if (state->error)
        {
            return false;
        }
        str = read_const_char(str, '}', state);
        if (state->error)
        {
            Read_state_clear_error(state);
            bool expect_key = true;
            while (expect_key)
            {
                char key[128] = { '\0' };
                str = read_string(str, key, 128, state);
                str = read_const_char(str, ':', state);
                if (strcmp(key, "buf_count") == 0)
                {
                    int64_t num = 0;
                    str = read_int(str, &num, state);
                    if (state->error)
                    {
                        return false;
                    }
                    if (num < 1 || num > KQT_BUFFERS_MAX)
                    {
                        Read_state_set_error(state,
                                 "Unsupported number of mixing buffers: %" PRId64, num);
                        return false;
                    }
                    if (!Song_set_buf_count(song, num))
                    {
                        Read_state_set_error(state,
                                 "Couldn't allocate memory for mixing buffers");
                        return false;
                    }
                }
                else if (strcmp(key, "mix_vol") == 0)
                {
                    str = read_double(str, &song->mix_vol_dB, state);
                    if (state->error)
                    {
                        return false;
                    }
                    if (!isfinite(song->mix_vol_dB) && song->mix_vol_dB != -INFINITY)
                    {
                        Read_state_set_error(state,
                                 "Invalid mixing volume: %f", song->mix_vol_dB);
                        song->mix_vol_dB = 0;
                        return false;
                    }
                    song->mix_vol = exp2(song->mix_vol_dB / 6);
                }
                else if (strcmp(key, "init_subsong") == 0)
                {
                    int64_t num = 0;
                    str = read_int(str, &num, state);
                    if (state->error)
                    {
                        return false;
                    }
                    if (num < 0 || num >= KQT_SUBSONGS_MAX)
                    {
                        Read_state_set_error(state,
                                 "Invalid initial Subsong number: %" PRId64, num);
                        return false;
                    }
                    Song_set_subsong(song, num);
                }
                else
                {
                    Read_state_set_error(state,
                             "Unrecognised key in composition info: %s", key);
                    return false;
                }
                if (state->error)
                {
                    return false;
                }
                check_next(str, state, expect_key);
            }
            str = read_const_char(str, '}', state);
            if (state->error)
            {
                return false;
            }
        }
    }
    for (int i = 0; i < KQT_SCALES_MAX; ++i)
    {
        char dir_name[] = "scale_0";
        snprintf(dir_name, 8, "scale_%01x", i);
        File_tree* index_tree = File_tree_get_child(tree, dir_name);
        if (index_tree != NULL)
        {
            Read_state_init(state, File_tree_get_path(index_tree));
            if (!File_tree_is_dir(index_tree))
            {
                Read_state_set_error(state,
                         "Scale at index %01x is not a directory", i);
                return false;
            }
            File_tree* notes_tree = File_tree_get_child(index_tree, "kunquats00");
            if (notes_tree != NULL)
            {
                Read_state_init(state, File_tree_get_path(notes_tree));
                if (!Song_create_notes(song, i))
                {
                    Read_state_set_error(state,
                             "Couldn't allocate memory for scale %01x", i);
                    return false;
                }
                Note_table* notes = Song_get_notes(song, i);
                assert(notes != NULL);
                Note_table_read(notes, notes_tree, state);
                if (state->error)
                {
                    Song_remove_notes(song, i);
                    return false;
                }
            }
        }
    }
    Order* order = Song_get_order(song);
    if (!Order_read(order, tree, state))
    {
        return false;
    }
    Pat_table* pats = Song_get_pats(song);
    if (!Pat_table_read(pats, tree, state))
    {
        return false;
    }
    Ins_table* insts = Song_get_insts(song);
    if (!Ins_table_read(insts, tree, state,
                        Song_get_bufs(song),
                        Song_get_voice_bufs(song),
                        Song_get_buf_count(song),
                        Song_get_buf_size(song),
                        Song_get_note_tables(song),
                        Song_get_active_notes(song),
                        32)) // TODO: make configurable
    {
        return false;
    }
    return true;
}


uint32_t Song_mix(Song* song, uint32_t nframes, Playdata* play)
{
    assert(song != NULL);
    assert(play != NULL);
    if (play->mode == STOP)
    {
        return 0;
    }
    if (nframes > song->buf_size && !play->silent)
    {
        nframes = song->buf_size;
    }
    if (!play->silent)
    {
        for (int i = 0; i < song->buf_count; ++i)
        {
            for (uint32_t k = 0; k < nframes; ++k)
            {
                song->bufs[i][k] = 0;
            }
        }
    }
    uint32_t mixed = 0;
    while (mixed < nframes && play->mode)
    {
        Pattern* pat = NULL;
        if (play->mode >= PLAY_SUBSONG)
        {
            int16_t pat_index = ORDER_NONE;
            Subsong* ss = Order_get_subsong(song->order, play->subsong);
            if (ss != NULL)
            {
                pat_index = Subsong_get(ss, play->order_index);
            }
            if (pat_index >= 0)
            {
                pat = Pat_table_get(song->pats, pat_index);
            }
        }
        else if (play->mode == PLAY_PATTERN && play->pattern >= 0)
        {
            pat = Pat_table_get(song->pats, play->pattern);
        }
        if (pat == NULL && play->mode != PLAY_EVENT)
        {
            if (play->mode < PLAY_SONG)
            {
                play->mode = STOP;
                break;
            }
            assert(play->mode == PLAY_SONG);
            if (play->subsong >= KQT_SUBSONGS_MAX - 1)
            {
                Playdata_set_subsong(play, 0);
                play->mode = STOP;
                break;
            }
            Playdata_set_subsong(play, play->subsong + 1);
            continue;
        }
        uint32_t proc_start = mixed;
        mixed += Pattern_mix(pat, nframes, mixed, play);
        if (play->mode == PLAY_EVENT)
        {
            continue;
        }
        Event* event = NULL;
        uint32_t proc_until = mixed;
        Event_queue_get(song->events, &event, &proc_until);
        // TODO: mix private instrument buffers
        while (proc_start < mixed)
        {
            assert(proc_until <= mixed);
            for (uint32_t i = proc_start; i < proc_until; ++i)
            {
                // TODO: modify buffer according to state
            }
            proc_start = proc_until;
            proc_until = mixed;
            while (Event_queue_get(song->events, &event, &proc_until))
            {
                // TODO: process events
                if (proc_start < mixed)
                {
                    break;
                }
            }
        }
        assert(!Event_queue_get(song->events, &event, &proc_until));
    }
    if (!play->silent)
    {
        for (int i = 0; i < song->buf_count; ++i)
        {
            for (uint32_t k = 0; k < mixed; ++k)
            {
                song->bufs[i][k] *= song->mix_vol;
                if (song->bufs[i][k] < play->min_amps[i])
                {
                    play->min_amps[i] = song->bufs[i][k];
                }
                if (song->bufs[i][k] > play->max_amps[i])
                {
                    play->max_amps[i] = song->bufs[i][k];
                }
                if (fabs(song->bufs[i][k]) > 1)
                {
                    ++play->clipped[i];
                }
            }
        }
    }
    play->play_frames += mixed;
    return mixed;
}


uint64_t Song_skip(Song* song, Playdata* play, uint64_t amount)
{
    assert(song != NULL);
    assert(play != NULL);
    bool orig_silent = play->silent;
    play->silent = true;
    uint64_t mixed = 0;
    while (mixed < amount)
    {
        uint64_t max_mix = amount - mixed;
        uint64_t nframes = MIN(max_mix, play->freq);
        uint32_t inc = Song_mix(song, nframes, play);
        mixed += inc;
        if (inc < Song_get_buf_size(song))
        {
            break;
        }
    }
    play->silent = orig_silent;
    return mixed;
}


void Song_set_mix_vol(Song* song, double mix_vol)
{
    assert(song != NULL);
    assert(isfinite(mix_vol) || mix_vol == -INFINITY);
    song->mix_vol_dB = mix_vol;
    song->mix_vol = exp2(mix_vol / 6);
    return;
}


double Song_get_mix_vol(Song* song)
{
    assert(song != NULL);
    return song->mix_vol_dB;
}


void Song_set_subsong(Song* song, uint16_t num)
{
    assert(song != NULL);
    assert(num < KQT_SUBSONGS_MAX);
    song->init_subsong = num;
    return;
}


uint16_t Song_get_subsong(Song* song)
{
    assert(song != NULL);
    return song->init_subsong;
}


bool Song_set_buf_count(Song* song, int count)
{
    assert(song != NULL);
    assert(count > 0);
    assert(count <= KQT_BUFFERS_MAX);
    if (song->buf_count == count)
    {
        return true;
    }
    else if (count < song->buf_count)
    {
        for (int i = count; i < song->buf_count; ++i)
        {
            xfree(song->priv_bufs[i]);
            song->priv_bufs[i] = song->bufs[i] = NULL;
            xfree(song->voice_bufs[i]);
            song->voice_bufs[i] = NULL;
        }
        // TODO: remove Instrument buffers
    }
    else
    {
        for (int i = song->buf_count; i < count; ++i)
        {
            song->priv_bufs[i] = xnalloc(kqt_frame, song->buf_size);
            if (song->priv_bufs[i] == NULL)
            {
                return false;
            }
            song->bufs[i] = song->priv_bufs[i];
            song->voice_bufs[i] = xnalloc(kqt_frame, song->buf_size);
            if (song->voice_bufs[i] == NULL)
            {
                return false;
            }
        }
        // TODO: create Instrument buffers
    }
    song->buf_count = count;
    return true;
}


int Song_get_buf_count(Song* song)
{
    assert(song != NULL);
    return song->buf_count;
}


bool Song_set_buf_size(Song* song, uint32_t size)
{
    assert(song != NULL);
    assert(size > 0);
    if (song->buf_size == size)
    {
        return true;
    }
    for (int i = 0; i < song->buf_count; ++i)
    {
        kqt_frame* new_buf = xrealloc(kqt_frame, size, song->priv_bufs[i]);
        if (new_buf == NULL)
        {
            if (i == 0) // first change failed -- keep the original state
            {
                return false;
            }
            if (size < song->buf_size)
            {
                song->buf_size = size;
            }
            return false;
        }
        song->priv_bufs[i] = new_buf;
        song->bufs[i] = song->priv_bufs[i];
        new_buf = xrealloc(kqt_frame, size, song->voice_bufs[i]);
        if (new_buf == NULL)
        {
            if (size < song->buf_size)
            {
                song->buf_size = size;
            }
            return false;
        }
        song->voice_bufs[i] = new_buf;
    }
    // TODO: resize Instrument buffers
    song->buf_size = size;
    return true;
}


uint32_t Song_get_buf_size(Song* song)
{
    assert(song != NULL);
    return song->buf_size;
}


kqt_frame** Song_get_bufs(Song* song)
{
    assert(song != NULL);
    return song->bufs;
}


kqt_frame** Song_get_voice_bufs(Song* song)
{
    assert(song != NULL);
    return song->voice_bufs;
}


Order* Song_get_order(Song* song)
{
    assert(song != NULL);
    return song->order;
}


Pat_table* Song_get_pats(Song* song)
{
    assert(song != NULL);
    return song->pats;
}


Ins_table* Song_get_insts(Song* song)
{
    assert(song != NULL);
    return song->insts;
}


Note_table** Song_get_note_tables(Song* song)
{
    assert(song != NULL);
    return song->notes;
}


Note_table* Song_get_notes(Song* song, int index)
{
    assert(song != NULL);
    assert(index >= 0);
    assert(index < KQT_SCALES_MAX);
    return song->notes[index];
}


Note_table** Song_get_active_notes(Song* song)
{
    assert(song != NULL);
    return song->active_notes;
}


bool Song_create_notes(Song* song, int index)
{
    assert(song != NULL);
    assert(index >= 0);
    assert(index < KQT_SCALES_MAX);
    if (song->notes[index] != NULL)
    {
        Note_table_clear(song->notes[index]);
        return true;
    }
    song->notes[index] = new_Note_table(440,
            Real_init_as_frac(REAL_AUTO, 2, 1));
    if (song->notes[index] == NULL)
    {
        return false;
    }
    return true;
}


void Song_remove_notes(Song* song, int index)
{
    assert(song != NULL);
    assert(index >= 0);
    assert(index < KQT_SCALES_MAX);
    if (song->notes[index] != NULL)
    {
        del_Note_table(song->notes[index]);
        song->notes[index] = NULL;
    }
    return;
}


Event_queue* Song_get_events(Song* song)
{
    assert(song != NULL);
    return song->events;
}


void del_Song(Song* song)
{
    assert(song != NULL);
    for (int i = 0; i < song->buf_count && song->priv_bufs[i] != NULL; ++i)
    {
        xfree(song->priv_bufs[i]);
    }
    for (int i = 0; i < song->buf_count && song->voice_bufs[i] != NULL; ++i)
    {
        xfree(song->voice_bufs[i]);
    }
    if (song->order != NULL)
    {
        del_Order(song->order);
    }
    if (song->pats != NULL)
    {
        del_Pat_table(song->pats);
    }
    if (song->insts != NULL)
    {
        del_Ins_table(song->insts);
    }
    for (int i = 0; i < KQT_SCALES_MAX; ++i)
    {
        if (song->notes[i] != NULL)
        {
            del_Note_table(song->notes[i]);
        }
    }
    if (song->events != NULL)
    {
        del_Event_queue(song->events);
    }
    xfree(song);
    return;
}

