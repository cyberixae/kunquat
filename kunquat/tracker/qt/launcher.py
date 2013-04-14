# -*- coding: utf-8 -*-

#
# Author: Toni Ruottu, Finland 2013
#
# This file is part of Kunquat.
#
# CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
#
# To the extent possible under law, Kunquat Affirmers have waived all
# copyright and related or neighboring rights to Kunquat.
#

from ui import Ui


class QtLauncher():

    def __init__(self, show=True):
        self._show = show
        self._ui_model = None
        self._queue_processor = None

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model

    def set_queue_processor(self, queue_processor):
        self._queue_processor = queue_processor

    def halt_ui(self):
        self._ui.halt()

    def run_ui(self):
        self._ui = Ui()
        self._ui.set_ui_model(self._ui_model)
        self._ui.set_queue_processor(self._queue_processor)
        if self._show == True:
            self._ui.show()
        self._ui.run()

