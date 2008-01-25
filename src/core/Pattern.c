

/*
 * Copyright 2008 Tomi Jylhä-Ollila
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
#include <stdio.h>
#include <assert.h>
#include <stdbool.h>

#include "Pattern.h"
#include <Playdata.h>
#include <Event_queue.h>
#include <Event.h>

#include <xmemory.h>


Pattern* new_Pattern(void)
{
	Pattern* pat = xalloc(Pattern);
	if (pat == NULL)
	{
		return NULL;
	}
	pat->global = new_Column(NULL);
	if (pat->global == NULL)
	{
		xfree(pat);
		return NULL;
	}
	for (int i = 0; i < PAT_CHANNELS; ++i)
	{
		pat->cols[i] = new_Column(NULL);
		if (pat->cols[i] == NULL)
		{
			for (--i; i >= 0; --i)
			{
				del_Column(pat->cols[i]);
			}
			del_Column(pat->global);
			xfree(pat);
			return NULL;
		}
	}
	Reltime_set(&pat->length, 16, 0);
	return pat;
}


Column* Pattern_col(Pattern* pat, int index)
{
	assert(pat != NULL);
	assert(index >= 0);
	assert(index < PAT_CHANNELS);
	return pat->cols[index];
}


Column* Pattern_global(Pattern* pat)
{
	assert(pat != NULL);
	return pat->global;
}


uint32_t Pattern_mix(Pattern* pat,
		uint32_t nframes,
		uint32_t offset,
		Playdata* play)
{
	assert(pat != NULL);
	assert(offset < nframes);
	assert(play != NULL);
	uint32_t mixed = offset;
	while (mixed < nframes
			// TODO: and we still want to mix this pattern
			&& Reltime_cmp(&play->pos, &pat->length) <= 0)
	{
		Event* next_global = Column_get(pat->global, &play->pos);
		Reltime* next_global_pos = NULL;
		if (next_global != NULL)
		{
			next_global_pos = Event_pos(next_global);
		}
		// - Evaluate global events
		while (next_global != NULL
				&& Reltime_cmp(next_global_pos, &play->pos) == 0)
		{
			if (Event_get_type(next_global) == EVENT_TYPE_GLOBAL_TEMPO)
			{
				Event_float(next_global, 0, &play->tempo);
			}
			if (EVENT_TYPE_IS_GENERAL(Event_get_type(next_global))
					|| EVENT_TYPE_IS_GLOBAL(Event_get_type(next_global)))
			{
				if (!Event_queue_ins(play->events, next_global, mixed))
				{
					// Queue is full, ignore remaining events... TODO: notify
					next_global = Column_get(pat->global,
							Reltime_add(RELTIME_AUTO, &play->pos,
									Reltime_set(RELTIME_AUTO, 0, 1)));
					if (next_global != NULL)
					{
						next_global_pos = Event_pos(next_global);
					}
					break;
				}
			}
			next_global = Column_get_next(pat->global);
			if (next_global != NULL)
			{
				next_global_pos = Event_pos(next_global);
			}
		}
		if (Reltime_cmp(&play->pos, &pat->length) >= 0)
		{
			assert(Reltime_cmp(&play->pos, &pat->length) == 0);
			Reltime_init(&play->pos);
			if (play->play == PLAY_PATTERN)
			{
				break;
			}
			++play->order_index;
			if (play->order_index >= PATTERNS_MAX)
			{
				play->order_index = 0;
				play->pattern = -1;
			}
			else
			{
				play->pattern = Order_get(play->order,
						play->subsong,
						play->order_index);
			}
			break;
		}
		assert(next_global == NULL || next_global_pos != NULL);
		uint32_t to_be_mixed = nframes - mixed;
		Reltime* limit = Reltime_fromframes(RELTIME_AUTO,
				to_be_mixed,
				play->tempo,
				play->freq);
		Reltime_add(limit, limit, &play->pos);
		// - Check for the end of pattern
		if (Reltime_cmp(&pat->length, limit) < 0)
		{
			Reltime_copy(limit, &pat->length);
			to_be_mixed = Reltime_toframes(
					Reltime_sub(RELTIME_AUTO, limit, &play->pos),
					play->tempo,
					play->freq);
		}
		// - Check first upcoming global event position to figure out how much we can mix for now
		if (next_global != NULL && Reltime_cmp(next_global_pos, limit) < 0)
		{
			assert(next_global_pos != NULL);
			Reltime_copy(limit, next_global_pos);
			to_be_mixed = Reltime_toframes(
					Reltime_sub(RELTIME_AUTO, limit, &play->pos),
					play->tempo,
					play->freq);
		}
		// - Tell each channel to set up Voices
		for (int i = 0; i < PAT_CHANNELS; ++i)
		{
			Channel_set_voices(play->channels[i],
					play->voice_pool,
					pat->cols[i],
					&play->pos,
					limit,
					mixed,
					play->tempo,
					play->freq);
		}
		// - Calculate the number of frames to be mixed
		assert(Reltime_cmp(&play->pos, limit) <= 0);
		if (to_be_mixed > nframes - mixed)
		{
			to_be_mixed = nframes - mixed;
		}
		// - Mix the Voice pool
		Voice_pool_mix(play->voice_pool, to_be_mixed + mixed, mixed, play->freq);
		// - Increment play->pos
		Reltime_copy(&play->pos, limit);
		mixed += to_be_mixed;
	}
	return mixed - offset;
}


void del_Pattern(Pattern* pat)
{
	assert(pat != NULL);
	for (int i = 0; i < PAT_CHANNELS; ++i)
	{
		del_Column(pat->cols[i]);
	}
	del_Column(pat->global);
	xfree(pat);
	return;
}

