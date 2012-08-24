# -*- coding: utf-8 -*-

#
# Author: Tomi Jylhä-Ollila, Finland 2010-2012
#
# This file is part of Kunquat.
#
# CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
#
# To the extent possible under law, Kunquat Affirmers have waived all
# copyright and related or neighboring rights to Kunquat.
#

from __future__ import division
from __future__ import print_function
from itertools import izip_longest, takewhile
import math
import string

from PyQt4 import QtGui, QtCore

import kunquat.tracker.kqt_limits as lim
import kunquat.tracker.scale as scale
import kunquat.tracker.timestamp as ts
import kunquat.tracker.trigtypes as ttypes


note_off_str = u'══'

hidden_types = ('n+', 'h')


class Trigger(list):

    def __init__(self, data, theme):
        list.__init__(self, data)
        self.set_type(data[0])
        self.colours = theme[0]
        self.fonts = theme[1]
        self.metrics = QtGui.QFontMetrics(self.fonts['trigger'])
        m_width = self.metrics.width('m')
        self.margin = m_width * 0.3
        self.padding = m_width * 0.15

    def set_type(self, ttype):
        self[0] = TriggerType(ttype)
        self.type_info = None
        if self[0].valid:
            name = self[0]
            if name.endswith('"'):
                name = name[:-1]
            self.type_info = ttypes.triggers[name]
            #lv = takewhile(lambda x: x[0],
            #               izip_longest(self.type_info, [self[1]]))
            #self[1] = None
            if self.type_info and not self[1]:
                self[1] = self.type_info[0][2]
            elif not self.type_info:
                self[1] = None
            """
            for limits, value in lv:
                cons, valid, default = limits
                try:
                    if valid(value):
                        self[1] = cons(value)
                    else:
                        self[1] = default
                except TypeError:
                    self[1] = default
            """
            if self[0] in ('c.gBn"', 'g.Bn"', 'd.Bn"'):
                self[1] = key_to_param(self[1], 'p_', '.jsonb')
            elif self[0] in ('c.gIn"', 'g.In"', 'd.In"'):
                self[1] = key_to_param(self[1], 'p_', '.jsoni')
            elif self[0] in ('c.gFn"', 'g.Fn"', 'd.Fn"'):
                self[1] = key_to_param(self[1], 'p_', '.jsonf')
            elif self[0] in ('c.gTn"', 'g.Tn"', 'd.Tn"'):
                self[1] = key_to_param(self[1], 'p_', '.jsont')
        #else:
        #    self[1] = list(fields)

    def flatten(self):
        if self[0] in ('c.gBn"', 'g.Bn"', 'd.Bn"'):
            return [self[0], param_to_key(self[1], 'p_', '.jsonb')]
        elif self[0] in ('c.gIn"', 'g.In"', 'd.In"'):
            return [self[0], param_to_key(self[1], 'p_', '.jsoni')]
        elif self[0] in ('c.gFn"', 'g.Fn"', 'd.Fn"'):
            return [self[0], param_to_key(self[1], 'p_', '.jsonf')]
        elif self[0] in ('c.gTn"', 'g.Tn"', 'd.Tn"'):
            return [self[0], param_to_key(self[1], 'p_', '.jsont')]
        return self

    def set_value(self, cursor_pos, value):
        assert cursor_pos < 2
        if self[0] not in hidden_types:
            if cursor_pos == 0:
                self.set_type(value)
                return
            #cursor_pos -= 1
        else:
            assert cursor_pos == 0
            cursor_pos = 1
        cons, valid, default = self.type_info[0]
        self[1] = value

    def cursor_area(self, index):
        start = self.margin
        if self[0] not in hidden_types:
            hw = self.metrics.width(self[0])
            if index == 0:
                return start, hw
            start += hw
            index -= 1
        else:
            # compensate for removal of trigger name
            start -= self.padding
        if self[1] != None:
            field = self[1]
            fw = self.field_width(field)
            if index == 0:
                return start + self.padding, fw - self.padding
            start += fw
            index -= 1
        assert round(start + self.margin - self.width()) == 0
        return start + self.margin, 0

    def get_field_info(self, cursor_pos):
        assert cursor_pos < 2
        if self[0] not in hidden_types:
            # ignore the trigger name
            if cursor_pos == 0:
                return self[0], lambda x: str(x) in ttypes.triggers
            #cursor_pos -= 1
        else:
            assert cursor_pos == 0
            cursor_pos = 1
        if 0 <= cursor_pos < 2:
            return self[cursor_pos], self.type_info[0][1]
        return None

    def paint(self, paint, rect, offset=0, cursor_pos=-1):
        init_offset = offset
        paint.setPen(self.colours['trigger_fg'])
        opt = QtGui.QTextOption()
        opt.setWrapMode(QtGui.QTextOption.NoWrap)
        opt.setAlignment(QtCore.Qt.AlignRight)

        offset += self.margin
        # paint the trigger type name
        if self[0] not in hidden_types:
            head_rect = QtCore.QRectF(rect)
            head_rect.moveLeft(head_rect.left() + offset)
            if self[0] == 'n-':
                type_width = self.metrics.width(note_off_str)
            else:
                type_width = self.metrics.width(self[0])
            head_rect.setWidth(type_width)
            head_rect = head_rect.intersect(rect)
            if offset < 0:
                if offset > -type_width:
                    self[0].paint(self.colours, paint, head_rect,
                                  opt, cursor_pos == 0)
            else:
                if head_rect.width() < type_width and \
                        head_rect.right() == rect.right():
                    opt.setAlignment(QtCore.Qt.AlignLeft)
                self[0].paint(self.colours, paint, head_rect,
                              opt, cursor_pos == 0)
            cursor_pos -= 1
            offset += type_width
        else:
            offset -= self.padding

        # paint the fields
        if self[1] != None:
            field = self[1]
            field_rect = QtCore.QRectF(rect)
            field_rect.moveLeft(rect.left() + offset + self.padding)
            field_width = self.field_width(field)
            field_rect.setWidth(field_width)
            field_rect = field_rect.intersect(rect)
            if field_rect.isValid():
                if field_rect.width() < field_width and \
                        field_rect.right() == rect.right():
                    opt.setAlignment(QtCore.Qt.AlignLeft)
                self.paint_field(paint, field, field_rect, opt,
                                 cursor_pos == 0)
            offset += field_width
            cursor_pos -= 1

        offset += self.margin
        if offset > 0:
            if self[0] == 'n+':
                paint.setPen(self.colours['trigger_note_on_fg'])
            elif self[0] == 'h':
                paint.setPen(self.colours['trigger_hit_fg'])
            elif self[0] == 'n-':
                paint.setPen(self.colours['trigger_note_off_fg'])
            else:
                paint.setPen(self.colours['trigger_fg'])
            left = max(rect.left() + init_offset, rect.left())
            right = min(rect.left() + offset, rect.right()) - 1
            if left < right:
                paint.drawLine(left, rect.top(),
                               right, rect.top())
#        if round((offset - init_offset) - self.width()) != 0:
#            print('offset change and width differ in', self, end=' -- ')
#            print(offset - init_offset, '!=', self.width(), end=', ')
#            print('diff:', (offset - init_offset) - self.width())
        return offset

    def paint_field(self, paint, field, rect, opt, cursor):
        s = self.field_str(field)
        back = self.colours['bg']
        if self[0] == 'n+':
            fore = self.colours['trigger_note_on_fg']
        elif self[0] == 'h':
            fore = self.colours['trigger_hit_fg']
        else:
            fore = self.colours['trigger_fg']
        if cursor:
            back, fore = fore, back
        paint.setBackground(back)
        paint.setPen(fore)
        paint.drawText(rect, s, opt)

    def field_str(self, field):
        event_name = self[0]
        if event_name.endswith('"'):
            event_name = event_name[:-1]
        event_type = ttypes.triggers[event_name]
        field_type = event_type[0][0] if event_type else None
        if field_type == ttypes.Note:
            try:
                cents = float(field)
            except ValueError:
                return field if field else "''"
            n, o, c = default_scale.get_display_info(cents)
            c = int(round(c))
            if c == 0:
                return '{0}{1}'.format(n, o)
            return '{0}{1}{2:+d}'.format(n, o, c)
        return field if field else "''"

    def field_width(self, field):
        return self.padding + self.metrics.width(self.field_str(field))

    def slots(self):
        if self[0] in hidden_types:
            return 1
        return 2 if self[1] != None else 1

    def width(self):
        field_width = self.field_width(self[1]) if self[1] != None else 0
        type_width = -self.padding
        if self[0] == 'n-':
            type_width = self.metrics.width(note_off_str)
        elif self[0] not in hidden_types:
            type_width = self.metrics.width(self[0])
        return type_width + field_width + 2 * self.margin


class TriggerType(str):

    def __init__(self, name):
        pass

    def valid(self, x):
        x = str(x)
        if x.endswith('"'):
            x = x[:-1]
        return x in ttypes.triggers

    def paint(self, colours, paint, rect, opt, cursor):
        if self == 'n-':
            fore = colours['trigger_note_off_fg']
        elif self.valid:
            fore = colours['trigger_type_fg']
        else:
            fore = colours['trigger_invalid_fg']
        back = colours['bg']
        if cursor:
            fore, back = back, fore
        paint.setBackground(back)
        paint.setPen(fore)
        paint.drawText(rect, self if self != 'n-' else note_off_str, opt)


default_scale = scale.Scale({
        'ref_pitch': 440 * 2**(3.0/12),
        'octave_ratio': ['/', [2, 1]],
        'notes': list(zip(('C', 'C#', 'D', 'D#', 'E', 'F',
                           'F#', 'G', 'G#', 'A', 'A#', 'B'),
                          (['c', cents] for cents in range(0, 1200, 100))))
    })


def key_to_param(key, prefix, suffix):
    last_index = key.index('/') + 1 if '/' in key else 0
    last_part = key[last_index:]
    if last_part.startswith(prefix) and last_part.endswith(suffix):
        last_part = last_part[len(prefix):-len(suffix)]
        return key[:last_index] + last_part
    return key


def param_to_key(param, prefix, suffix):
    last_index = param.index('/') + 1 if '/' in param else 0
    last_part = param[last_index:]
    if not last_part.startswith(prefix):
        last_part = 'p_' + last_part
    if not last_part.endswith(suffix):
        last_part = last_part + suffix
    return param[:last_index] + last_part

