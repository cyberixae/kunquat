# Lean models of the Kunquat control layer

Experimental Lean 4 models of parts of `src/lib`, with machine-checked proofs
about their behaviour. Each model follows the branch structure of the C code it
describes, so the two can be compared line by line.

## Building

Requires Lean 4.35.0 (see `lean-toolchain`); no other dependencies.

    lake build

A successful build means every theorem has been checked.

## Contents

### `Kunquat/Tstamp.lean` — `src/lib/mathnum/Tstamp.c`

Models `Tstamp_add`, `Tstamp_sub`, `Tstamp_cmp` and `Tstamp_min` over
mathematical integers, and proves, for valid timestamps
(`0 ≤ rem < KQT_TSTAMP_BEAT`):

- The `rassert`s in `Tstamp_add` and `Tstamp_sub` never fail.
- One normalisation branch in each of `Tstamp_add` and `Tstamp_sub` is
  unreachable.
- Addition and subtraction are exact, and each value has exactly one valid
  representation. As a consequence `(a + b) - b = a`, so slide end times never
  drift.
- `Tstamp_cmp` orders timestamps by the time they denote, and `Tstamp_min`
  returns the earlier one.
- The intermediate `int32_t` remainder sums cannot overflow.
- `beats` changes by at most one carry or borrow. `int64_t` overflow of
  `beats` is not checked by the C code; callers must keep results in range.

The model is marked `noncomputable`: it exists only for proofs and is not
compiled into the library.

### `Kunquat/Tstamp64.lean` — the same functions in machine integers

Implements `Tstamp_add`, `Tstamp_sub` and `Tstamp_cmp` with the C widths
(`Int64` beats, `Int32` remainder) and proves that they agree with the model:

- `add` and `sub` agree whenever the beat sum or difference, with room for a
  carry or borrow, fits in `int64_t` (`AddInRange`, `SubInRange`). Outside
  that range the C code has signed overflow, which is undefined behaviour.
- `cmp` agrees on all inputs.

These are exported to C as `kqt_lean_tstamp_add_beats`, `..._add_rem`,
`..._sub_beats`, `..._sub_rem` and `kqt_lean_tstamp_cmp`. They take and return
only `uint64_t` and `uint32_t` (the bit patterns of `int64_t` and `int32_t`),
so no Lean objects cross the boundary and there is no reference counting to
get wrong. With `@[inline]` on the operations, the generated functions are
straight-line integer code with no heap allocation.

### `Kunquat/Jump.lean` — jumps in `src/lib/player/Player_seq.c`

Models the jump state machine: `m.jc` (jump counter), `m.jp`/`m.jr` (jump
target), `mj` (jump) and the jump contexts kept per trigger position, step by
step as in `Player_process_cgiters` and `Event_master_jump_process`. Control
events are left out because triggers ignore them outside infinite mode.

- `play_ends`: playback always reaches the end of the song, for any song and
  any `m.jc` values, including values computed at playback time. This covers
  nested loops, where an exhausted inner jump is re-armed on each outer pass,
  and loops that cross or jump forwards over each other.
- `ends_within`: it ends within `(C + 3) ^ n` steps, where `n` is the number
  of trigger slots and `C` the largest jump counter (32767 in Kunquat). The
  bound is astronomically large but finite.
- `play` is playback as a total Lean function: Lean accepts its definition
  only because of the termination proof.

The proof uses one digit per trigger position, with later positions more
significant: each step lowers the digit of the current position and does not
raise any later one. Re-arming a jump requires playback to come back to it
from a later position, which uses up a jump there.

#### A bug in the C player, found through the model and fixed

The model looks up jump contexts in the current state. The C code used to look
up the next one once per render slice, within the current pattern instance.
When a slice moved into another pattern instance, an existing jump context
there was missed. Depending on the audio buffer size, `mj` then ran again and
adding a second context with the same key failed an assertion in
`AAtree_attach` (Kunquat's `rassert` is enabled in all builds, so the player
aborted), or playback never stopped. `Player_seq.c` now repeats the lookup
whenever playback enters another pattern instance, and only treats a trigger
as an active jump if the context belongs to the same pattern instance.

`src/test/player.c` (`Jump_context_in_next_pattern_instance_is_found`) and
`test/jump_context_crash.c` are regression tests for it; the model's
`crashSong` example shows the expected behaviour.

## Calling the Lean code from C

Before the first call, C must initialize the Lean runtime and the module, and
every other thread that calls in must be registered. `lean.h` does not
declare these functions, so callers declare them:

    extern void lean_initialize_runtime_module(void);
    extern void lean_initialize_thread(void);
    extern void lean_finalize_thread(void);
    extern lean_object* initialize_kunquat_Kunquat(uint8_t builtin);

    lean_initialize_runtime_module();
    lean_object* res = initialize_kunquat_Kunquat(1);
    /* check lean_io_result_is_ok(res), then lean_dec_ref(res) */
    lean_io_mark_end_initialization();

Skipping module initialization would not crash, but would silently compute
with wrong values: constants such as `BEAT32` are set by the initializer.

## Tstamp differential test

`test/run.sh` builds the Lean library, the original `src/lib/mathnum/Tstamp.c`
and the harness `test/tstamp_diff.c`, and compares the two implementations on
every pair of boundary values and 4 million random cases on 4 threads. It also
calls the Lean functions with 2 million arbitrary inputs, including invalid
remainders that the C code would assert on, to check they never crash. The
script fails if the generated C contains panic paths.

    test/run.sh                                    # plain
    test/run.sh -fsanitize=address,undefined       # memory errors, UB
    test/run.sh -fsanitize=thread                  # data races

`test/lsan.supp` suppresses a fixed 128-byte report from Lean's standard
library, which allocates a few big-integer constants at initialization and
never frees them by design.

## Jump tests

`test/run_jump.sh <libkunquat directory>` compares the jump model with the C
player: `test/jump_diff.py` generates random songs of `m.jc`, `m.jp`, `m.jr`
and `mj` triggers, half of them in one pattern instance and half over several
pattern instances with jumps between them, and checks that the playback time
predicted by the model (`JumpSim.lean`, built as `jumpsim`) equals the time
the C player plays (`test/jump_play.c`), with buffer sizes that used to crash.
It then runs the crash regression test.

Before the fix, this comparison found the bug on its own: on 300 random
songs, about half of them multi-pattern, the old player aborted on 5 and
never stopped on another.

## Limitations

The theorems are checked by Lean, and the exported code is generated from the
same definitions they are about. What remains trusted is the Lean compiler
and runtime, and the hand-written C glue (initialization and declarations).
The correspondence between `Tstamp64` and `src/lib/mathnum/Tstamp.c` is by
inspection, backed by the differential test.

The jump model abstracts playback to a sequence of trigger slots, so it says
nothing about timing within a slice, pattern delays or tempo. Its link to the
C code is by inspection plus the playback-time comparison.
