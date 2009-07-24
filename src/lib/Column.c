

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
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>

#include <Reltime.h>
#include <Event_global_set_tempo.h>
#include <Event_voice_note_on.h>
#include <Event_voice_note_off.h>
#include <Column.h>

#include <xmemory.h>


typedef struct Event_list
{
    Event* event;
    struct Event_list* prev;
    struct Event_list* next;
} Event_list;


struct Column_iter
{
    uint32_t version;
    Column* col;
    AAiter* tree_iter;
    Event_list* elist;
};


struct Column
{
    kqt_Reltime len;
    uint32_t version;
    Column_iter* edit_iter;
    AAtree* events;
};


static Event_list* new_Event_list(Event_list* nil, Event* event);

static Event_list* Event_list_init(Event_list* elist);

static int Event_list_cmp(Event_list* list1, Event_list* list2);

static void del_Event_list(Event_list* elist);


static Event_list* new_Event_list(Event_list* nil, Event* event)
{
    assert(!(nil == NULL) || (event == NULL));
    assert(!(event == NULL) || (nil == NULL));
    Event_list* elist = xalloc(Event_list);
    if (elist == NULL)
    {
        return NULL;
    }
    if (nil == NULL)
    {
        assert(event == NULL);
        elist->event = NULL;
        elist->prev = elist->next = elist;
    }
    else
    {
        assert(event != NULL);
        elist->event = event;
        elist->prev = elist->next = nil;
    }
    return elist;
}


static Event_list* Event_list_init(Event_list* elist)
{
    assert(elist != NULL);
    elist->prev = elist->next = elist;
    return elist;
}


static int Event_list_cmp(Event_list* list1, Event_list* list2)
{
    assert(list1 != NULL);
    assert(list2 != NULL);
    Event* ev1 = list1->next->event;
    Event* ev2 = list2->next->event;
    assert(ev1 != NULL);
    assert(ev2 != NULL);
    return kqt_Reltime_cmp(Event_get_pos(ev1), Event_get_pos(ev2));
}


Column_iter* new_Column_iter(Column* col)
{
    Column_iter* iter = xalloc(Column_iter);
    if (iter == NULL)
    {
        return NULL;
    }
    iter->col = col;
    iter->version = (col != NULL) ? col->version : 0;
    AAtree* events = (col != NULL) ? col->events : NULL;
    iter->tree_iter = new_AAiter(events);
    if (iter->tree_iter == NULL)
    {
        xfree(iter);
        return NULL;
    }
    iter->elist = NULL;
    return iter;
}


void Column_iter_change_col(Column_iter* iter, Column* col)
{
    assert(iter != NULL);
    assert(col != NULL);
    iter->col = col;
    iter->version = col->version;
    AAiter_change_tree(iter->tree_iter, col->events);
    iter->elist = NULL;
    return;
}


Event* Column_iter_get(Column_iter* iter, const kqt_Reltime* pos)
{
    assert(iter != NULL);
    assert(pos != NULL);
    if (iter->col == NULL)
    {
        return NULL;
    }
    iter->version = iter->col->version;
    Event* event = &(Event){ .type = EVENT_TYPE_NONE };
    kqt_Reltime_copy(&event->pos, pos);
    Event_list* key = Event_list_init(&(Event_list){ .event = event });
    iter->elist = AAiter_get(iter->tree_iter, key);
    if (iter->elist == NULL)
    {
        return NULL;
    }
    assert(iter->elist->event == NULL);
    assert(iter->elist->next != iter->elist);
    iter->elist = iter->elist->next;
    assert(iter->elist->event != NULL);
    return iter->elist->event;
}


Event* Column_iter_get_next(Column_iter* iter)
{
    assert(iter != NULL);
    if (iter->elist == NULL || iter->col == NULL)
    {
        return NULL;
    }
    if (iter->version != iter->col->version)
    {
        iter->elist = NULL;
        iter->version = iter->col->version;
        return NULL;
    }
    assert(iter->elist->event != NULL);
    assert(iter->elist != iter->elist->next);
    iter->elist = iter->elist->next;
    if (iter->elist->event != NULL)
    {
        return iter->elist->event;
    }
    iter->elist = AAiter_get_next(iter->tree_iter);
    if (iter->elist == NULL)
    {
        return NULL;
    }
    assert(iter->elist->event == NULL);
    assert(iter->elist->next != iter->elist);
    iter->elist = iter->elist->next;
    assert(iter->elist->event != NULL);
    return iter->elist->event;
}


void del_Column_iter(Column_iter* iter)
{
    assert(iter != NULL);
    del_AAiter(iter->tree_iter);
    xfree(iter);
    return;
}


Column* new_Column(kqt_Reltime* len)
{
    Column* col = xalloc(Column);
    if (col == NULL)
    {
        return NULL;
    }
    col->version = 1;
    col->events = new_AAtree((int (*)(void*, void*))Event_list_cmp,
            (void (*)(void*))del_Event_list);
    if (col->events == NULL)
    {
        xfree(col);
        return NULL;
    }
    col->edit_iter = new_Column_iter(col);
    if (col->edit_iter == NULL)
    {
        del_AAtree(col->events);
        xfree(col);
        return NULL;
    }
    if (len != NULL)
    {
        kqt_Reltime_copy(&col->len, len);
    }
    else
    {
        kqt_Reltime_set(&col->len, INT64_MAX, 0);
    }
    return col;
}


#define break_if(error)   \
    do                    \
    {                     \
        if ((error))      \
        {                 \
            return false; \
        }                 \
    } while (false)

bool Column_read(Column* col, File_tree* tree, Read_state* state)
{
    assert(col != NULL);
    assert(tree != NULL);
    assert(state != NULL);
    if (state->error)
    {
        return false;
    }
    Read_state_init(state, File_tree_get_path(tree));
    if (!File_tree_is_dir(tree))
    {
        Read_state_set_error(state, "Column is not a directory");
        return false;
    }
    bool is_global = strcmp(File_tree_get_name(tree), "global_column") == 0;
    File_tree* event_tree = NULL;
    if (!is_global)
    {
        event_tree = File_tree_get_child(tree, "voice_events.json");
    }
    else
    {
        event_tree = File_tree_get_child(tree, "global_events.json");
    }
    if (event_tree == NULL)
    {
        return true;
    }
    if (File_tree_is_dir(event_tree))
    {
        Read_state_init(state, "Event list is a directory");
        return false;
    }
    char* str = File_tree_get_data(event_tree);

    str = read_const_char(str, '[', state); // start of Column
    break_if(state->error);

    str = read_const_char(str, ']', state); // check of empty Column
    if (!state->error)
    {
        return true;
    }
    Read_state_clear_error(state);

    bool expect_event = true;
    while (expect_event)
    {
        str = read_const_char(str, '[', state);
        break_if(state->error);

        kqt_Reltime* pos = kqt_Reltime_init(KQT_RELTIME_AUTO);
        str = read_reltime(str, pos, state);
        break_if(state->error);

        str = read_const_char(str, ',', state);
        break_if(state->error);

        int64_t type = 0;
        str = read_int(str, &type, state);
        break_if(state->error);
        if (!EVENT_TYPE_IS_VALID(type))
        {
            Read_state_set_error(state, "Invalid Event type: %" PRId64 "\n", type);
            return false;
        }
        if ((is_global && EVENT_TYPE_IS_VOICE(type)) ||
                (!is_global && EVENT_TYPE_IS_GLOBAL(type)))
        {
            Read_state_set_error(state,
                     "Incorrect Event type for %s column", is_global ? "global" : "note");
            return false;
        }

        Event* event = new_Event(type, pos);
        if (event == NULL)
        {
            Read_state_set_error(state, "Couldn't allocate memory for Event");
            return false;
        }
        str = Event_read(event, str, state);
        if (state->error)
        {
            del_Event(event);
            return false;
        }
        if (!Column_ins(col, event))
        {
            Read_state_set_error(state, "Couldn't insert Event");
            del_Event(event);
            return false;
        }
        
        str = read_const_char(str, ']', state);
        break_if(state->error);

        check_next(str, state, expect_event);
    }

    str = read_const_char(str, ']', state);
    if (state->error)
    {
        return false;
    }
    return true;
}

#undef break_if


bool Column_write(Column* col, FILE* out, Write_state* state)
{
    assert(col != NULL);
    assert(out != NULL);
    assert(state != NULL);
    (void)col;
    (void)out;
    if (state->error)
    {
        return false;
    }
    return false;
}


bool Column_ins(Column* col, Event* event)
{
    assert(col != NULL);
    assert(event != NULL);
    ++col->version;
    Event_list* key = Event_list_init(&(Event_list){ .event = event });
    Event_list* ret = AAtree_get(col->events, key);
    if (ret == NULL || kqt_Reltime_cmp(Event_get_pos(event),
            Event_get_pos(ret->next->event)) != 0)
    {
        Event_list* nil = new_Event_list(NULL, NULL);
        if (nil == NULL)
        {
            return false;
        }
        Event_list* node = new_Event_list(nil, event);
        if (node == NULL)
        {
            del_Event_list(nil);
            return false;
        }
        nil->prev = nil->next = node;
        node->prev = node->next = nil;
        if (!AAtree_ins(col->events, nil))
        {
            del_Event_list(nil);
            del_Event_list(node);
            return false;
        }
        return true;
    }
    assert(ret->next != ret);
    assert(ret->prev != ret);
    assert(ret->event == NULL);
    Event_list* node = new_Event_list(ret, event);
    if (node == NULL)
    {
        return false;
    }
    node->prev = ret->prev;
    node->next = ret;
    ret->prev->next = node;
    ret->prev = node;
    return true;
}


bool Column_move(Column* col, Event* event, unsigned int index)
{
    assert(col != NULL);
    assert(event != NULL);
    ++col->version;
    Event_list* key = Event_list_init(&(Event_list){ .event = event });
    Event_list* target = AAtree_get(col->events, key);
    if (target == NULL)
    {
        assert(false);
        return false;
    }
    assert(target->event == NULL);
    Event_list* src = NULL;
    Event_list* shifted = NULL;
    Event_list* cur = target->next;
    assert(cur != NULL);
    assert(cur->event != NULL);
    unsigned int idx = 0;
    while (cur != target)
    {
        if (idx == index)
        {
            shifted = cur;
        }
        if (event == cur->event)
        {
            src = cur;
            if (src == shifted)
            {
                return false;
            }
            --idx;
        }
        cur = cur->next;
        ++idx;
    }
    assert(src != NULL);
    src->prev->next = src->next;
    src->next->prev = src->prev;
    if (shifted == NULL)
    {
        src->prev = target->prev;
        assert(target->prev->prev != NULL);
        assert(target->prev->prev != target);
        target->prev->next = src;
        target->prev = src;
    }
    else
    {
        assert(src != shifted);
        src->next = shifted;
        src->prev = shifted->prev;
        assert(src->next != src);
        assert(src->prev != src);
        if (src->prev != NULL)
        {
            src->prev->next = src;
        }
        else
        {
            target->next = src;
        }
        if (src->next != NULL)
        {
            src->next->prev = src;
        }
        else
        {
            target->prev = src;
        }
    }
    return true;
}


bool Column_remove(Column* col, Event* event)
{
    assert(col != NULL);
    assert(event != NULL);
    ++col->version;
    Event_list* key = Event_list_init(&(Event_list){ .event = event });
    Event_list* target = AAtree_get(col->events, key);
    if (target == NULL || kqt_Reltime_cmp(Event_get_pos(event),
            Event_get_pos(target->next->event)) != 0)
    {
        return false;
    }
    assert(target->event == NULL);
    Event_list* elist = target->next;
    while (elist != target && elist->event != event)
    {
        elist = elist->next;
        assert(elist != NULL);
    }
    if (elist == target)
    {
        return false;
    }
    Event_list* eprev = elist->prev;
    Event_list* enext = elist->next;
    if (eprev != enext)
    {
        assert(eprev != target || enext != target);
        del_Event(elist->event);
        xfree(elist);
        eprev->next = enext;
        enext->prev = eprev;
        return true;
    }
    assert(eprev == target);
    assert(enext == target);
    target = AAtree_remove(col->events, key);
    assert(target != NULL);
    del_Event_list(target);
    return true;
}


bool Column_remove_row(Column* col, kqt_Reltime* pos)
{
    assert(col != NULL);
    assert(pos != NULL);
    ++col->version;
    bool modified = false;
    Event* target = Column_iter_get(col->edit_iter, pos);
    while (target != NULL && kqt_Reltime_cmp(Event_get_pos(target), pos) == 0)
    {
        modified = Column_remove(col, target);
        assert(modified);
        target = Column_iter_get(col->edit_iter, pos);
    }
    return modified;
}


bool Column_remove_block(Column* col, kqt_Reltime* start, kqt_Reltime* end)
{
    assert(col != NULL);
    assert(start != NULL);
    assert(end != NULL);
    ++col->version;
    bool modified = false;
    Event* target = Column_iter_get(col->edit_iter, start);
    while (target != NULL && kqt_Reltime_cmp(Event_get_pos(target), end) <= 0)
    {
        modified = Column_remove_row(col, Event_get_pos(target));
        assert(modified);
        target = Column_iter_get(col->edit_iter, start);
    }
    return modified;
}


bool Column_shift_up(Column* col, kqt_Reltime* pos, kqt_Reltime* len)
{
    assert(col != NULL);
    assert(pos != NULL);
    assert(len != NULL);
    ++col->version;
    bool removed = false;
    kqt_Reltime* del_end = kqt_Reltime_set(KQT_RELTIME_AUTO, 0, 1);
    del_end = kqt_Reltime_sub(del_end, len, del_end);
    del_end = kqt_Reltime_add(del_end, pos, del_end);
    removed = Column_remove_block(col, pos, del_end);
    Event* target = Column_iter_get(col->edit_iter, pos);
    while (target != NULL)
    {
        kqt_Reltime* ev_pos = Event_get_pos(target);
        kqt_Reltime_sub(ev_pos, ev_pos, len);
        target = Column_iter_get_next(col->edit_iter);
    }
    return removed;
}


void Column_shift_down(Column* col, kqt_Reltime* pos, kqt_Reltime* len)
{
    assert(col != NULL);
    assert(pos != NULL);
    assert(len != NULL);
    ++col->version;
    Event* target = Column_iter_get(col->edit_iter, pos);
    while (target != NULL)
    {
        kqt_Reltime* ev_pos = Event_get_pos(target);
        kqt_Reltime_add(ev_pos, ev_pos, len);
        target = Column_iter_get_next(col->edit_iter);
    }
    return;
}


void Column_clear(Column* col)
{
    assert(col != NULL);
    ++col->version;
    AAtree_clear(col->events);
    Column_iter_change_col(col->edit_iter, col);
    return;
}


void Column_set_length(Column* col, kqt_Reltime* len)
{
    assert(col != NULL);
    assert(len != NULL);
    kqt_Reltime_copy(&col->len, len);
    return;
}


kqt_Reltime* Column_length(Column* col)
{
    assert(col != NULL);
    return &col->len;
}


void del_Column(Column* col)
{
    assert(col != NULL);
    del_AAtree(col->events);
    del_Column_iter(col->edit_iter);
    xfree(col);
    return;
}


static void del_Event_list(Event_list* elist)
{
    assert(elist != NULL);
    assert(elist->event == NULL);
    Event_list* cur = elist->next;
    assert(cur->event != NULL);
    while (cur->event != NULL)
    {
        Event_list* next = cur->next;
        assert(cur->event != NULL);
        del_Event(cur->event);
        xfree(cur);
        cur = next;
    }
    assert(cur == elist);
    xfree(cur);
    return;
}

