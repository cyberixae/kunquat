# -*- coding: utf-8 -*-

#
# Authors: Toni Ruottu, Finland 2013
#          Tomi Jylhä-Ollila, Finland 2014
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

from keyboardmapper import KeyboardMapper
from octavebutton import OctaveButton


class OctaveSelector(QFrame):

    def __init__(self):
        QFrame.__init__(self)
        self.setFocusPolicy(Qt.TabFocus)
        self._ui_model = None
        self._typewriter_manager = None
        self._keyboard_mapper = KeyboardMapper()

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._typewriter_manager = ui_model.get_typewriter_manager()
        self._keyboard_mapper.set_ui_model(ui_model)
        self._update()

    def unregister_updaters(self):
        layout = self.layout()
        layout_items = [layout.itemAt(i) for i in xrange(layout.count())]
        for item in layout_items:
            button = item.widget()
            if button:
                button.unregister_updaters()

    def _update(self):
        layout = self._get_layout()
        self.setLayout(layout)

    def _get_layout(self):
        octave_count = self._typewriter_manager.get_octave_count()
        row = QHBoxLayout()
        for i in range(octave_count):
            button = self._get_button(i)
            row.addWidget(button)
        row.addStretch(1)
        return row

    def _get_button(self, octave_id):
        button = OctaveButton(octave_id)
        button.set_ui_model(self._ui_model)
        return button

    def keyPressEvent(self, event):
        if not self._keyboard_mapper.process_typewriter_button_event(event):
            event.ignore()

    def keyReleaseEvent(self, event):
        if not self._keyboard_mapper.process_typewriter_button_event(event):
            event.ignore()


