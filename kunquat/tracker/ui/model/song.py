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

from patterninstance import PatternInstance


class Song():

    def __init__(self, song_id):
        assert song_id
        self._song_id = song_id
        self._store = None
        self._controller = None

    def set_controller(self, controller):
        self._store = controller.get_store()
        self._controller = controller

    def get_existence(self):
        key = '{}/p_manifest.json'.format(self._song_id)
        manifest = self._store[key]
        return (type(manifest) == type({}))

    def get_system_count(self):
        return len(self._get_order_list())

    def get_pattern_instance(self, system_num):
        order_list = self._get_order_list()
        pattern_num, instance_num = order_list[system_num]
        pattern_instance = PatternInstance(pattern_num, instance_num)
        pattern_instance.set_controller(self._controller)
        return pattern_instance

    def _get_order_list(self):
        assert self.get_existence()
        key = '{}/p_order_list.json'.format(self._song_id)
        try:
            order_list = self._store[key]
        except KeyError:
            order_list = [] # TODO: get default from libkunquat
        return order_list


