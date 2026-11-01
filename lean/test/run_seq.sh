#!/bin/sh
# Compare the Lean sequencer with the C player.
#
# Usage: lean/test/run_seq.sh <directory containing libkunquat.so> [module count] [seed]
#
# Build libkunquat first (see run_jump.sh). Runs seq_diff.py, which plays
# random modules with the Lean sequencer (Kunquat/Seq.lean, built as seqsim)
# and with libkunquat (seq_play.c), and checks that they report the same
# events at the same frames.
#
# Requires the Lean toolchain (lake) on PATH, a C compiler and python3.

set -eu

if [ $# -lt 1 ]; then
    sed -n '2,4p' "$0" | sed 's/^# //' >&2
    exit 2
fi

LIB_DIR=$(cd "$1" && pwd)
COUNT=${2:-300}
SEED=${3:-1}
LEAN_DIR=$(cd "$(dirname "$0")/.." && pwd)
ROOT=$(cd "$LEAN_DIR/.." && pwd)
BUILD="$LEAN_DIR/.lake/build/seq_tests"
mkdir -p "$BUILD"

(cd "$LEAN_DIR" && lake build seqsim)

CC=${CC:-cc}
$CC -std=gnu99 -O1 -g -Wall -Wextra -I"$ROOT/src/include" \
    "$LEAN_DIR/test/seq_play.c" -o "$BUILD/seq_play" \
    -L"$LIB_DIR" -lkunquat -Wl,-rpath,"$LIB_DIR" -lm

python3 "$LEAN_DIR/test/seq_diff.py" \
    "$LEAN_DIR/.lake/build/bin/seqsim" "$BUILD/seq_play" "$COUNT" "$SEED"
