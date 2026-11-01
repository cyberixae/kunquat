#!/bin/sh
# Build and run the jump tests against libkunquat.
#
# Usage: lean/test/run_jump.sh <directory containing libkunquat.so> [song count]
#
# Build libkunquat first, for example with
#   ./make.py --disable-tests --disable-python-tests --disable-tracker \
#       --disable-player --disable-export --disable-examples
# which puts the library in build/src/lib.
#
# Runs:
# - jump_diff.py: random songs played by the C player and the Lean model must
#   have the same playback time.
# - jump_context_crash.c: a known crash in the C player (see that file). It is
#   reported but does not fail this script; once it passes, it should.
#
# Requires the Lean toolchain (lake) on PATH, a C compiler and python3.

set -eu

if [ $# -lt 1 ]; then
    sed -n '2,4p' "$0" | sed 's/^# //' >&2
    exit 2
fi

LIB_DIR=$(cd "$1" && pwd)
COUNT=${2:-300}
LEAN_DIR=$(cd "$(dirname "$0")/.." && pwd)
ROOT=$(cd "$LEAN_DIR/.." && pwd)
BUILD="$LEAN_DIR/.lake/build/jump_tests"
mkdir -p "$BUILD"

(cd "$LEAN_DIR" && lake build jumpsim)

CC=${CC:-cc}
LINK="-L$LIB_DIR -lkunquat -Wl,-rpath,$LIB_DIR -lm"
$CC -std=gnu99 -O1 -g -Wall -Wextra -I"$ROOT/src/include" \
    "$LEAN_DIR/test/jump_play.c" -o "$BUILD/jump_play" $LINK
$CC -std=gnu99 -O1 -g -Wall -Wextra -I"$ROOT/src/include" \
    "$LEAN_DIR/test/jump_context_crash.c" -o "$BUILD/jump_context_crash" $LINK

echo "== Model against C player"
python3 "$LEAN_DIR/test/jump_diff.py" \
    "$LEAN_DIR/.lake/build/bin/jumpsim" "$BUILD/jump_play" "$COUNT"

echo "== Known crash (jump_context_crash.c)"
if "$BUILD/jump_context_crash"; then
    echo "The known crash no longer occurs: make this test fail on regression."
else
    echo "Known crash still present (expected for now)."
fi
