#!/usr/bin/env python3
"""
Differential test of the jump model against the C player.

Generates random one-pattern songs made of m.jc, m.jr and mj triggers, and
compares the playback time predicted by the Lean model (jumpsim) with the time
measured by playing the song with libkunquat (jump_play).

Usage: jump_diff.py <jumpsim> <jump_play> [song count] [seed]
"""

import random
import subprocess
import sys


MAX_BEATS = 2000  # skip songs that would take long to render


def random_song(rng):
    length = rng.randint(2, 8)
    slots = []
    for row in range(length):
        for _ in range(rng.choice([0, 0, 1, 1, 2, 3])):
            slots.append([row, rng.choice(['jc', 'jc', 'jr', 'mj', 'mj', 'mj'])])
    if not slots or slots[0][0] != 0:
        # Jumps default to row 0; keep a slot there so the row time is exact.
        slots.insert(0, [0, 'jc'])
    rows_with_slots = sorted({row for row, _ in slots})
    lines = [str(length)]
    for row, kind in slots:
        if kind == 'jc':
            lines.append('{} jc {}'.format(row, rng.choice([0, 1, 1, 2, 3])))
        elif kind == 'jr':
            lines.append('{} jr {}'.format(row, rng.choice(rows_with_slots)))
        else:
            lines.append('{} mj'.format(row))
    return '\n'.join(lines) + '\n'


TOO_LONG = 'too long'


def run(cmd, song):
    p = subprocess.run(cmd, input=song, capture_output=True, text=True, timeout=600)
    if p.returncode == 3:
        return TOO_LONG
    if p.returncode != 0:
        return 'error: ' + (p.stderr.strip() or 'exit {}'.format(p.returncode))
    return int(p.stdout.strip())


def main():
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    jumpsim, jump_play = sys.argv[1], sys.argv[2]
    count = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rng = random.Random(seed)

    compared = skipped = mismatches = 0
    total_beats = 0
    for i in range(count):
        song = random_song(rng)
        expected = run([jumpsim], song)
        if expected == TOO_LONG:
            skipped += 1
            continue
        if not isinstance(expected, int):
            print('song {}: model {}'.format(i, expected))
            mismatches += 1
            continue
        if expected > MAX_BEATS:
            skipped += 1
            continue
        buf_size = rng.choice(['256', '1000', '4096', '24000'])
        actual = run([jump_play, buf_size], song)
        compared += 1
        total_beats += expected
        if actual != expected:
            mismatches += 1
            print('song {} (buffer {}): model {} beats, C player {}'.format(
                i, buf_size, expected, actual))
            print(song)

    print('{} songs compared ({} beats of playback), {} skipped as too long, '
          '{} mismatches'.format(compared, total_beats, skipped, mismatches))
    return 0 if mismatches == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
