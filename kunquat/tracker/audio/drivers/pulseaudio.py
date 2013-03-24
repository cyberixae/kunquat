# -*- coding: utf-8 -*-

#
# Authors: Tomi Jylhä-Ollila, Finland 2013
#          Toni Ruottu, Finland 2013
#
# This file is part of Kunquat.
#
# CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
#
# To the extent possible under law, Kunquat Affirmers have waived all
# copyright and related or neighboring rights to Kunquat.
#

from __future__ import print_function
import sys
import time
import Queue

from kunquat.extras.pulseaudio_async import Async

class Pulseaudio():

    def __init__(self):
        self._ag = None
        self._pa = Async(
                'Kunquat Tracker',
                'Editor output',
                self._pa_callback)
        self._buffer = Queue.Queue()
        self._workspace = ([],[])
        self._pa.init()

    def set_audio_generator(self, ag):
        self._ag = ag

    def put_audio(self, audio):
        self._buffer.put(audio)

    def _next(self, nframes):
        self._ag.generate(nframes)

    def _split_list_at(self, lst, i):
        first = lst[:i]
        second = lst[i:]
        return (first, second)

    def _split_audio_at(self, audio, i):
        (left, right) = audio
        (left1, left2) = self._split_list_at(left, i)
        (right1, right2) = self._split_list_at(right, i)
        audio1 = (left1, right1)
        audio2 = (left2, right2)
        return (audio1, audio2)

    def _join_audio(self, audio1, audio2):
        (left1, right1) = audio1
        (left2, right2) = audio2
        left = left1 + left2
        right = right1 + right2
        audio = (left, right)
        return audio

    def _update_workspace(self):
        items = self._buffer.qsize()
        for _ in range(items):
            fresh_audio = self._buffer.get()
            self._workspace = self._join_audio(self._workspace, fresh_audio)

    def _read_workspace(self, nframes):
        (left, right) = self._workspace
        assert len(left) == len(right)
        frames = len(left)
        if frames > nframes:
            (audio_data, remainder) = self._split_audio_at(self._workspace, nframes)
        else:
            audio_data = self._workspace
            remainder = ([],[])
        self._workspace = remainder
        return audio_data

    def _pa_callback(self, nframes):
        self._next(nframes)
        self._update_workspace()
        audio_data = self._read_workspace(nframes)
        return audio_data

    def start(self):
        #self._next(20)
        self._pa.play()

    def stop(self):
        self._pa.stop()

