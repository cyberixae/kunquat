#!/bin/sh
# Build and run the Tstamp differential test.
#
# Usage: lean/test/run.sh [extra C flags]
# For example, to run under sanitizers:
#   lean/test/run.sh -fsanitize=address,undefined
#   lean/test/run.sh -fsanitize=thread
#
# Requires the Lean toolchain (lake, lean) on PATH and a C compiler (cc, or
# $CC). Everything is compiled and linked with the system compiler, because the
# compiler bundled with Lean ships neither system headers nor sanitizer
# runtimes. The Lean runtime libraries are linked explicitly.

set -eu

LEAN_DIR=$(cd "$(dirname "$0")/.." && pwd)
ROOT=$(cd "$LEAN_DIR/.." && pwd)
BUILD="$LEAN_DIR/.lake/build/tstamp_diff"
mkdir -p "$BUILD"

(cd "$LEAN_DIR" && lake build Kunquat:static)

# The exported code must have no panic paths: a Lean panic does not stop the
# program but returns a default value, which C would silently use.
if grep -l "lean_panic" "$LEAN_DIR"/.lake/build/ir/Kunquat/*.c; then
    echo "error: generated C contains panic paths" >&2
    exit 1
fi

LEAN_PREFIX=$(lean --print-prefix)
CC=${CC:-cc}
CFLAGS="-std=gnu99 -O2 -g -Wall -Wextra -Werror=implicit-function-declaration $*"
INCLUDES="-I$ROOT/src/lib -I$ROOT/src/include -I$LEAN_PREFIX/include"

$CC $CFLAGS $INCLUDES -c "$ROOT/src/lib/mathnum/Tstamp.c" -o "$BUILD/Tstamp.o"
$CC $CFLAGS $INCLUDES -c "$ROOT/src/lib/debug/assert.c" -o "$BUILD/assert.o"
$CC $CFLAGS $INCLUDES -c "$LEAN_DIR/test/tstamp_diff.c" -o "$BUILD/tstamp_diff.o"

$CC "$@" -o "$BUILD/tstamp_diff" \
    "$BUILD/tstamp_diff.o" "$BUILD/Tstamp.o" "$BUILD/assert.o" \
    "$LEAN_DIR/.lake/build/lib/libkunquat_Kunquat.a" \
    -L"$LEAN_PREFIX/lib/lean" -L"$LEAN_PREFIX/lib" \
    -Wl,--start-group -lInit -lleanrt -Wl,--end-group \
    -Wl,-Bstatic -lc++ -lc++abi -lunwind -lgmp -luv -Wl,-Bdynamic \
    -lpthread -ldl -lm

LSAN_OPTIONS="suppressions=$LEAN_DIR/test/lsan.supp${LSAN_OPTIONS:+:$LSAN_OPTIONS}" \
UBSAN_OPTIONS="halt_on_error=1:print_stacktrace=1${UBSAN_OPTIONS:+:$UBSAN_OPTIONS}" \
    "$BUILD/tstamp_diff"
