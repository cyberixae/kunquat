# -*- coding: utf-8 -*-

#
# Author: Tomi Jylhä-Ollila, Finland 2011
#
# This file is part of Kunquat.
#
# CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
#
# To the extent possible under law, Kunquat Affirmers have waived all
# copyright and related or neighboring rights to Kunquat.
#

from __future__ import division, print_function

from PyQt4 import QtCore, QtGui

import kunquat.editor.kqt_limits as lim


class DSPs(QtGui.QSplitter):

    def __init__(self, project, base, parent=None):
        QtGui.QSplitter.__init__(self, parent)
        self._project = project
        self.addWidget(QtGui.QLabel('dsp list'))
        self.addWidget(QtGui.QLabel('dsp editor'))
        self.set_base(base)

    def set_base(self, base):
        self._base = base

    def sync(self):
        self.set_base(base)


