# -*- coding: utf-8 -*-

#
# Authors: Toni Ruottu, Finland 2013
#          Tomi Jylhä-Ollila, Finland 2013-2014
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


class OctaveButton(QPushButton):

    def __init__(self, octave_id):
        QPushButton.__init__(self)
        self._octave_id = octave_id
        self._typewriter_manager = None
        self._ui_manager = None
        self._updater = None

        self.setCheckable(True)
        self.setFixedSize(QSize(60, 30))
        self.setToolTip('Select octave (Ctrl + O: next, Ctrl + Shift + O: previous)')
        layout = QHBoxLayout(self)
        octavename = QLabel()
        self._octavename = octavename
        octavename.setAlignment(Qt.AlignCenter)
        layout.addWidget(octavename)
        led = QLabel()
        self._led = led
        self._led.setFixedWidth(10)
        layout.addWidget(led)
        layout.setAlignment(Qt.AlignCenter)

        QObject.connect(self, SIGNAL('clicked()'), self._select_octave)

    def _select_octave(self):
        self._typewriter_manager.set_octave(self._octave_id)

    def set_ui_model(self, ui_model):
        self._updater = ui_model.get_updater()
        self._updater.register_updater(self._perform_updates)
        self._ui_manager = ui_model.get_ui_manager()
        self._typewriter_manager = ui_model.get_typewriter_manager()
        self._button_model = self._typewriter_manager.get_octave_button_model(
                self._octave_id)
        octave_name = self._button_model.get_name()
        self._octavename.setText(octave_name)

    def unregister_updaters(self):
        self._updater.unregister_updater(self._perform_updates)

    def _update_pressed(self):
        old_block = self.blockSignals(True)
        if self._button_model.is_selected():
            self.setChecked(True)
        else:
            self.setChecked(False)
        self.blockSignals(old_block)

    def update_leds(self):
        selected_control = self._ui_manager.get_selected_control()
        if selected_control == None:
            return
        notes = selected_control.get_active_notes()
        is_on = 0
        for note in notes.itervalues():
            closest = self._typewriter_manager.get_closest_keymap_pitch(note)
            pitches = self._typewriter_manager.get_pitches_by_octave(self._octave_id)
            if closest in pitches:
                is_on = 1
        if is_on:
            self._led.setText('*')
        else:
            self._led.setText('')

    def _perform_updates(self, signals):
        if 'signal_octave' in signals:
            self._update_pressed()
        self.update_leds()


