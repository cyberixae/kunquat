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

## Limitations

The proofs are about the Lean model, not the compiled C. The correspondence
between the two is by inspection; differential testing of the C functions
against the model would strengthen it.
