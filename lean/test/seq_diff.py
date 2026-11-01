#!/usr/bin/env python3
"""
Differential test of the Lean sequencer against the C player.

Generates random modules (several pattern instances and columns, note, tempo
and jump triggers), plays each with the Lean sequencer (seqsim) and with
libkunquat (seq_play), and checks that:

* both report the same events, with the same channels and values, in the
  same order;
* every event happens, by the Lean sequencer, within the frames of the C
  play call that reported it. A play call that renders fewer frames than
  requested (because it stopped at a jump, a tempo change or the end) may also
  report the events at the frame just after the ones it rendered;
* both play for the same number of frames.

Usage: seq_diff.py <seqsim> <seq_play> [module count] [seed]
"""

import json
import random
import subprocess
import sys


TEMPOS = [60, 80, 90, 100, 120, 150, 160, 180, 200, 240]  # divide 72000
CHUNKS = ['1', '7', '64', '1000', '4096']
MAX_FRAMES = 500000  # skip modules that would take long to play


def random_module(rng):
    pattern_count = rng.randint(1, 4)
    lengths = [rng.randint(1, 12) for _ in range(pattern_count)]
    order = list(range(pattern_count))
    rng.shuffle(order)
    min_len = min(lengths)

    lines = ['order ' + ' '.join(map(str, order))]
    for p, length in enumerate(lengths):
        lines.append('pattern {} {}'.format(p, length))
        trigs = []
        for _ in range(rng.choice([0, 1, 2, 3, 4, 6])):
            col = rng.choice([0, 0, 1, 2, 5])
            row = rng.randrange(length)
            kind = rng.choice(['n+', 'n+', 'm.t', 'm.jc', 'm.jc', 'm.jp', 'm.jr', 'mj', 'mj', 'mj'])
            if kind == 'n+':
                arg = ' {}'.format(rng.randint(-24, 24) * 100)
            elif kind == 'm.t':
                arg = ' {}'.format(rng.choice(TEMPOS))
            elif kind == 'm.jc':
                arg = ' {}'.format(rng.choice([0, 1, 1, 2, 3]))
            elif kind == 'm.jp':
                # Sometimes a pattern that does not exist: jumping there stops
                # playback.
                arg = ' {}'.format(rng.randrange(pattern_count + 1))
            elif kind == 'm.jr':
                arg = ' {}'.format(rng.randrange(min_len))
            else:
                arg = ''
            trigs.append((row, 'trig {} {} {} {}{}'.format(p, col, row, kind, arg)))
        # Triggers of a column must be in row order; keep the generated order
        # within a row.
        trigs.sort(key=lambda t: t[0])
        lines.extend(t[1] for t in trigs)
    return '\n'.join(lines) + '\n'


def run(cmd, module):
    try:
        p = subprocess.run(cmd, input=module, capture_output=True, text=True,
                timeout=60)
    except subprocess.TimeoutExpired:
        return 1, '', 'timed out after 60 s'
    return p.returncode, p.stdout, p.stderr.strip()


def lean_events(output):
    events, total = [], None
    for line in output.splitlines():
        if line.startswith('end '):
            total = int(line.split()[1])
        else:
            frame, ch, ev = line.split(' ', 2)
            events.append((int(frame), int(ch), json.loads(ev)))
    return events, total


def c_events(output):
    events, total = [], None
    for line in output.splitlines():
        if line.startswith('end '):
            total = int(line.split()[1])
        else:
            _, first, count, evs = line.split(' ', 3)
            for ch, ev in json.loads(evs):
                events.append([int(first), int(count), ch, ev, False])
    if events:
        events[-1][4] = True  # possibly reported by the final play call
    return events, total


def compare(expected, actual, chunk):
    """Returns a description of the first difference, or None."""
    exp_events, exp_total = expected
    act_events, act_total = actual
    for i, (exp, act) in enumerate(zip(exp_events, act_events)):
        frame, ch, ev = exp
        first, count, act_ch, act_ev, final = act
        if (ch, ev) != (act_ch, act_ev):
            return 'event {}: Lean {} on channel {}, C {} on channel {}'.format(
                    i, ev, ch, act_ev, act_ch)
        # A play call that ends early processes the row it stopped at.
        last = first + count if final or count < chunk else first + count - 1
        if not first <= frame <= last:
            return 'event {} {}: Lean frame {}, C play call frames {}-{}'.format(
                    i, ev, frame, first, last)
    if len(exp_events) != len(act_events):
        return 'Lean reports {} events, C {}'.format(len(exp_events), len(act_events))
    if exp_total != act_total:
        return 'Lean plays {} frames, C {}'.format(exp_total, act_total)
    return None


def main():
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    seqsim, seq_play = sys.argv[1], sys.argv[2]
    count = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rng = random.Random(seed)

    compared = skipped = mismatches = events = 0
    for i in range(count):
        module = random_module(rng)
        chunk = rng.choice(CHUNKS)

        code, out, err = run([seqsim], module)
        if code == 3:
            skipped += 1
            continue
        if code != 0:
            print('module {}: seqsim failed: {}'.format(i, err))
            mismatches += 1
            continue
        expected = lean_events(out)
        if expected[1] > MAX_FRAMES:
            skipped += 1
            continue

        code, out, err = run([seq_play, chunk, str(2 * expected[1] + 10000)], module)
        compared += 1
        events += len(expected[0])
        diff = ('C player failed: ' + err) if code != 0 else compare(expected, c_events(out), int(chunk))
        if diff:
            mismatches += 1
            print('module {} (play calls of {} frames): {}'.format(i, chunk, diff))
            print(module)

    print('{} modules compared ({} events), {} skipped as too long, {} mismatches'.format(
            compared, events, skipped, mismatches))
    return 0 if mismatches == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
