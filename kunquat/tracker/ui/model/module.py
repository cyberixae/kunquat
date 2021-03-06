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

from instrument import Instrument
from control import Control
from album import Album
from song import Song
from pattern import Pattern


class Module():

    def __init__(self):
        self._updater = None
        self._session = None
        self._store = None
        self._controller = None
        self._ui_model = None
        self._instruments = {}

    def set_controller(self, controller):
        self._updater = controller.get_updater()
        self._session = controller.get_session()
        self._store = controller.get_store()
        self._controller = controller

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model

    def get_control_ids(self):
        try:
            input_map = self._store['p_control_map.json']
        except KeyError:
            input_map = []
        control_ids = set()
        for (control_number, _) in input_map:
            control_id = 'control_{0:02x}'.format(control_number)
            control_ids.add(control_id)
        return control_ids

    def get_control(self, control_id):
        control = Control(control_id)
        control.set_controller(self._controller)
        control.set_ui_model(self._ui_model)
        return control

    def get_instrument(self, instrument_id):
        instrument = Instrument(instrument_id)
        instrument.set_controller(self._controller)
        return instrument

    def get_instrument_ids(self):
        instrument_ids = set()
        for key in self._store.keys():
            if key.startswith('ins_'):
                instrument_id = key.split('/')[0]
                instrument_ids.add(instrument_id)
        return instrument_ids

    def get_instruments(self, validate=True):
        instrument_ids = self.get_instrument_ids()
        all_instruments = [self.get_instrument(i) for i in instrument_ids]
        #all_instruments = self._instruments.values()
        #if validate:
        #    valid = [i for i in all_instruments if i.get_existence()]
        #    return [] #valid
        return all_instruments

    def get_album(self):
        album = Album()
        album.set_controller(self._controller)
        if not album.get_existence():
            return None
        return album

    def set_path(self, path):
        self._session.set_module_path(path)

    def get_path(self):
        return self._session.get_module_path()

    def execute_load(self, task_executer):
        assert not self.is_saving()
        task = self._controller.get_task_load_module(self.get_path())
        task_executer(task)

    def execute_create_sandbox(self, task_executer):
        assert not self.is_saving()
        self._controller.create_sandbox()
        kqtifile = self._controller.get_share().get_default_instrument()
        task = self._controller.get_task_load_instrument(kqtifile)
        task_executer(task)

    def is_saving(self):
        return self._session.is_saving()

    def start_save(self):
        assert not self.is_saving()
        self._session.set_saving(True)
        self._store.set_saving(True)
        self._updater.signal_update(set(['signal_start_save_module']))

    def flush(self, callback):
        self._store.flush(callback)

    def execute_save(self, task_executer):
        assert self.is_saving()
        module_path = self._session.get_module_path()
        task = self._controller.get_task_save_module(module_path)
        task_executer(task)

    def finish_save(self):
        self._store.set_saving(False)
        self._session.set_saving(False)


