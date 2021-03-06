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

"""A wrapper for the simple PulseAudio library.

This module provides limited support for the simple PulseAudio
interface. Designed for Kunquat music tools, the module only exists
because there is no widespread Python wrapper yet. As soon as one
becomes available in major distributions, this module will be removed.

"""


from __future__ import print_function
import ctypes

from pulseaudio_def import *

__all__ = ['Simple', 'PulseAudioError']


class Simple(object):

    """An interface for a simple PulseAudio connection.

    Public methods:
    write -- Write audio data.
    drain -- Wait until all data written is actually played.

    """

    def __init__(self,
                 client_name,
                 stream_name,
                 rate=48000,
                 latency=0.2):
        """Create a new PulseAudio connection.

        Arguments:
        client_name -- A descriptive name for the client.
        stream_name -- A descriptive name for the stream.

        Optional arguments:
        rate        -- Audio rate in frames per second (default: 48000).
        latency     -- Desired latency in seconds (default: 0.2).  The
                       actual latency may differ.

        Exceptions:
        PulseAudioError -- Raised if the PulseAudio call fails.

        """
        assert type(client_name) == str
        assert type(stream_name) == str
        assert rate >= 1
        assert rate <= 192000
        assert latency > 0

        self._rate = int(rate)
        self._channels = 2
        self._latency = int(latency * 1000000)

        ss = SampleSpec(PA_SAMPLE_FLOAT32NE, self._rate, self._channels)
        buf_attr = BufferAttr(
                ctypes.c_uint32(-1), # maxlength
                _simple.pa_usec_to_bytes(self._latency, ctypes.byref(ss)),
                ctypes.c_uint32(-1), # prebuf
                ctypes.c_uint32(-1), # minreq
                ctypes.c_uint32(-1), # fragsize
                )
        error = ctypes.c_int(0)

        # Create connection
        self._connection = _simple.pa_simple_new(
                None, # server name
                client_name,
                PA_STREAM_PLAYBACK,
                None, # sink name
                stream_name,
                ctypes.byref(ss),
                None, # channel map
                ctypes.byref(buf_attr),
                ctypes.byref(error))
        if not self._connection:
            raise PulseAudioError(_simple.pa_strerror(error))

    def write(self, *data):
        """Write audio data to the output stream.

        Arguments:
        data -- The output buffers, each channel as a separate
                parameter.

        Exceptions:
        PulseAudioError -- Raised if the PulseAudio call fails.
        ValueError      -- Wrong number of output buffers, or the
                           buffer lengths do not match.

        """
        if len(data) != self._channels:
            raise ValueError('Wrong number of output channel buffers')
        frame_count = len(data[0])
        cdata = (ctypes.c_float * (frame_count * self._channels))()
        for channel in xrange(self._channels):
            if len(data[channel]) != frame_count:
                raise ValueError('Output channel buffer lengths do not match')
            cdata[channel::self._channels] = data[channel]
        bytes_per_frame = 4 * self._channels
        error = ctypes.c_int(0)
        if _simple.pa_simple_write(self._connection,
                                   cdata,
                                   bytes_per_frame * frame_count,
                                   ctypes.byref(error)) < 0:
            raise PulseAudioError(_simple.pa_strerror(error))

    def drain(self):
        """Wait until all data written is actually played.

        Exceptions:
        PulseAudioError -- Raised if the PulseAudio call fails.

        """
        error = ctypes.c_int(0)
        if _simple.pa_simple_drain(self._connection, ctypes.byref(error)) < 0:
            raise PulseAudioError(_simple.pa_strerror(error))

    def __del__(self):
        if self._connection:
            _simple.pa_simple_free(self._connection)
        self._connection = None


_simple = ctypes.CDLL('libpulse-simple.so')

_pa_usec = ctypes.c_uint64

_simple.pa_strerror.argtypes = [ctypes.c_int]
_simple.pa_strerror.restype = ctypes.c_char_p

_simple.pa_usec_to_bytes.argtypes = [_pa_usec, ctypes.POINTER(SampleSpec)]
_simple.pa_usec_to_bytes.restype = ctypes.c_size_t

_simple.pa_simple_new.argtypes = [
        ctypes.c_char_p,
        ctypes.c_char_p,
        ctypes.c_int, # pa_stream_direction_t
        ctypes.c_char_p,
        ctypes.c_char_p,
        ctypes.POINTER(SampleSpec),
        ctypes.c_void_p, # channel map
        ctypes.POINTER(BufferAttr),
        ctypes.POINTER(ctypes.c_int)]
_simple.pa_simple_new.restype = ctypes.c_void_p

_simple.pa_simple_free.argtypes = [ctypes.c_void_p]

_simple.pa_simple_write.argtypes = [
        ctypes.c_void_p,
        ctypes.c_void_p,
        ctypes.c_size_t,
        ctypes.POINTER(ctypes.c_int)]
_simple.pa_simple_write.restype = ctypes.c_int

_simple.pa_simple_drain.argtypes = [
        ctypes.c_void_p,
        ctypes.POINTER(ctypes.c_int)]
_simple.pa_simple_drain.restype = ctypes.c_int


