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

from instrument import Instrument
from slot import Slot


class Module():

    def __init__(self):
        self._updater = None
        self._store = None
        self._controller = None
        self._model = None
        self._instruments = {}

    def set_controller(self, controller):
        self._updater = controller.get_updater()
        self._store = controller.get_store()
        self._controller = controller

    def set_model(self, model):
        self._model = model

    def get_slot_ids(self):
        try:
            input_map = self._store['p_ins_input.json']
        except KeyError:
            input_map = []
        slot_ids = set()
        for (slot_number, _) in input_map:
            slot_id = 'slot_{0:02x}'.format(slot_number)
            slot_ids.add(slot_id)
        return slot_ids

    def get_slot(self, slot_id):
        slot = Slot(slot_id)
        slot.set_controller(self._controller)
        slot.set_model(self._model)
        return slot

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

