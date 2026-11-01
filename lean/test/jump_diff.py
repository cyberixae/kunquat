#!/usr/bin/env python3
"""
Differential test of the jump model against the C player.

Generates random songs made of m.jc, m.jp, m.jr and mj triggers, half of them
in one pattern instance and half spread over several with jumps between them,
and compares the playback time predicted by the Lean model (jumpsim) with the time
measured by playing the song with libkunquat (jump_play).

Usage: jump_diff.py <jumpsim> <jump_play> [song count] [seed]
"""

import random
import subprocess
import sys


MAX_BEATS = 2000  # skip songs that would take long to render


def random_song(rng):
    if rng.random() < 0.5:
        return random_one_pattern_song(rng)
    return random_multi_pattern_song(rng)


def random_multi_pattern_song(rng):
    lengths = [rng.randint(1, 3) for _ in range(rng.randint(2, 4))]
    total = sum(lengths)
    # m.jp defaults to the current pattern instance, which the model does not
    # track, so set a jump target before anything else.
    lines = [' '.join(map(str, lengths)), '0 jt {}'.format(rng.randrange(total))]
    for time in range(total):
        for _ in range(rng.choice([0, 0, 1, 1, 2])):
            kind = rng.choice(['jc', 'jc', 'jt', 'mj', 'mj', 'mj'])
            if kind == 'jc':
                lines.append('{} jc {}'.format(time, rng.choice([0, 1, 1, 2, 3])))
            elif kind == 'jt':
                lines.append('{} jt {}'.format(time, rng.randrange(total)))
            else:
                lines.append('{} mj'.format(time))
    return '\n'.join(lines) + '\n'


def random_one_pattern_song(rng):
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
    try:
        p = subprocess.run(cmd, input=song, capture_output=True, text=True,
                timeout=60)
    except subprocess.TimeoutExpired:
        return 'error: timed out after 60 s'
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
        buf_size = rng.choice(['256', '1000', '4000', '4096', '12000', '24000'])
        # Allow some slack, but notice quickly if the player does not stop.
        actual = run([jump_play, buf_size, str(2 * expected + 16)], song)
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
