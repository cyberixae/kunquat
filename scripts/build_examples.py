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

from __future__ import print_function
import os.path

import command


def build_examples(builder):
    build_dir = os.path.join('build', 'examples')
    command.make_dirs(builder, build_dir, echo='')

    example_dir = os.path.join('examples')

    packages = {
            'kqtc00': 'example.kqt.bz2',
            'kqti00': 'example_ins.kqti.bz2',
            'kqte00': 'example_effect.kqte.bz2',
            'kqts00': 'example_scale.kqts.bz2',
        }

    echo_prefix = '\n   Building example files\n\n'
    for src, dest in packages.iteritems():
        dest_path = os.path.join(build_dir, dest)
        echo = echo_prefix + 'Building {}'.format(dest)
        if command.run_command(
                builder,
                'tar',
                'cj', '--format=ustar',
                '-f', dest_path,
                '--directory', example_dir,
                src,
                echo=echo):
            echo_prefix = ''

    # Copy the example instrument to share
    # TODO: remove once we figure out the instrument stuff
    ins_name = 'example_ins.kqti.bz2'
    default_ins_path = os.path.join(build_dir, ins_name)
    share_target = os.path.join('share', 'kunquat', 'instruments', ins_name)
    command.copy(builder, default_ins_path, share_target, echo='')


