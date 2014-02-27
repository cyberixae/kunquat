# -*- coding: utf-8 -*-

#
# Author: Tomi Jylhä-Ollila, Finland 2014
#
# This file is part of Kunquat.
#
# CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
#
# To the extent possible under law, Kunquat Affirmers have waived all
# copyright and related or neighboring rights to Kunquat.
#

from PyQt4.QtCore import *
from PyQt4.QtGui import *


# TODO: Define alternatives for different environments if/when needed
_TYPEWRITER_MAP = {}

_TYPEWRITER_MAP.update(dict((11 + x, (0, x)) for x in xrange(9)))
_TYPEWRITER_MAP.update(dict((24 + x, (1, x)) for x in xrange(10)))
_TYPEWRITER_MAP.update(dict((39 + x, (2, x)) for x in xrange(7)))
_TYPEWRITER_MAP.update(dict((52 + x, (3, x)) for x in xrange(7)))


class KeyboardMapper():

    def __init__(self):
        self._ui_model = None
        self._typewriter_manager = None

        self._typewriter_map = _TYPEWRITER_MAP

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._typewriter_manager = ui_model.get_typewriter_manager()

    def process_typewriter_button_event(self, event):
        scancode = event.nativeScanCode()
        button = self.get_typewriter_button_model(scancode)
        if button and event.modifiers() == Qt.NoModifier:
            if event.isAutoRepeat():
                return True
            if event.type() == QEvent.KeyPress:
                button.press()
            elif event.type() == QEvent.KeyRelease:
                button.release()
        return False

    def get_typewriter_button_model(self, scancode):
        try:
            row, index = self._typewriter_map[scancode]
        except KeyError:
            return None

        button = self._typewriter_manager.get_button_model(row, index)
        return button


