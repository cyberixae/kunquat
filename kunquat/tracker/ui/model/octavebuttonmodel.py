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

class OctaveButtonModel():

    def __init__(self, octave_id):
        self._controller = None
        self._session = None
        self._ui_model = None
        self._typewriter_manager = None
        self._notation_manager = None

        self._octave_id = octave_id

    def set_controller(self, controller):
        self._controller = controller
        self._session = controller.get_session()

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._typewriter_manager = ui_model.get_typewriter_manager()
        self._notation_manager = ui_model.get_notation_manager()

    def get_name(self):
        notation = self._notation_manager.get_notation()
        return notation.get_octave_name(self._octave_id)

    def select(self):
        self._typewriter_manager.set_octave(self._octave_id)

    def is_selected(self):
        return (self._octave_id == self._session.get_octave_id())


