# -*- coding: utf-8 -*-

#
# Author: Tomi Jylhä-Ollila, Finland 2010-2013
#
# This file is part of Kunquat.
#
# CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
#
# To the extent possible under law, Kunquat Affirmers have waived all
# copyright and related or neighboring rights to Kunquat.
#

from PyQt4 import QtGui, QtCore

import kunquat.tracker.kqt_limits as lim
from pattern import Pattern
import kunquat.tracker.timestamp as ts
from kunquat.tracker.timestamp_spin import TimestampSpin


class PatternEditor(QtGui.QWidget):

    def __init__(self,
                 project,
                 playback_manager,
                 section_manager,
                 pattern_changed_slot,
                 pattern_offset_changed_slot,
                 octave_spin,
                 instrument_spin,
                 typewriter,
                 parent=None):
        QtGui.QWidget.__init__(self, parent)
        self._project = project
        section_manager.connect(self.section_changed)
        layout = QtGui.QVBoxLayout(self)
        layout.setMargin(0)
        layout.setSpacing(0)

        self._pattern = Pattern(project,
                                section_manager,
                                playback_manager,
                                pattern_offset_changed_slot,
                                octave_spin,
                                instrument_spin,
                                typewriter)
        layout.addWidget(self._pattern, 1)

        QtCore.QObject.connect(self._pattern,
                               QtCore.SIGNAL('patternChanged(int, int)'),
                               pattern_changed_slot)

    def init(self):
        self._pattern.init()

    def section_changed(self, song, system):
        pattern = self._project._composition.get_pattern(song, system)
        if pattern != None:
            key = 'pat_{0:03d}/p_pattern.json'.format(pattern[0])

    def sync(self):
        self._pattern.sync()


