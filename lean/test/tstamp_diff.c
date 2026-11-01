/*
 * Differential test: the Lean-generated Tstamp functions against the original
 * C implementation in src/lib/mathnum/Tstamp.c.
 *
 * Also exercises the Lean runtime boundary: runtime and module initialization,
 * calls from several threads, and calls with arbitrary (invalid) inputs, which
 * must not crash.
 */

#include <lean/lean.h>

#include <mathnum/Tstamp.h>

#include <inttypes.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>


// Lean exports (lean/Kunquat/Tstamp64.lean). Lean passes Int64 and Int32 as
// uint64_t and uint32_t; the bit patterns are the same as int64_t and int32_t.
extern uint64_t kqt_lean_tstamp_add_beats(uint64_t, uint32_t, uint64_t, uint32_t);
extern uint32_t kqt_lean_tstamp_add_rem(uint64_t, uint32_t, uint64_t, uint32_t);
extern uint64_t kqt_lean_tstamp_sub_beats(uint64_t, uint32_t, uint64_t, uint32_t);
extern uint32_t kqt_lean_tstamp_sub_rem(uint64_t, uint32_t, uint64_t, uint32_t);
extern uint32_t kqt_lean_tstamp_cmp(uint64_t, uint32_t, uint64_t, uint32_t);

extern lean_object* initialize_kunquat_Kunquat(uint8_t builtin);

// Lean runtime functions that C callers must declare themselves; lean.h
// does not declare them.
extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);


#define THREAD_COUNT 4
#define RANDOM_CASES_PER_THREAD 1000000
#define GARBAGE_CASES_PER_THREAD 100000


typedef struct { uint64_t s; } Rng;

static uint64_t rng_next(Rng* r)
{
    // splitmix64
    uint64_t z = (r->s += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}


static const int64_t beat_samples[] =
{
    0, 1, -1, 2, -2, 1000, -1000,
    INT64_MAX / 2, INT64_MIN / 2, INT64_MAX / 2 + 1, INT64_MIN / 2 - 1,
    INT64_MAX - 1, INT64_MIN + 1, INT64_MAX - 2, INT64_MIN + 2,
};

static const int32_t rem_samples[] =
{
    0, 1, 2, KQT_TSTAMP_BEAT / 2, KQT_TSTAMP_BEAT / 2 + 1,
    KQT_TSTAMP_BEAT - 2, KQT_TSTAMP_BEAT - 1,
};

#define COUNT(a) ((int)(sizeof(a) / sizeof((a)[0])))


static int64_t random_beats(Rng* r)
{
    switch (rng_next(r) % 4)
    {
        case 0: return beat_samples[rng_next(r) % COUNT(beat_samples)];
        case 1: return (int64_t)(rng_next(r) % 2001) - 1000;
        case 2: return (int64_t)(rng_next(r) >> 2) - (INT64_MAX >> 2);
        default: return (int64_t)rng_next(r);
    }
}

static int32_t random_rem(Rng* r)
{
    if (rng_next(r) % 2 == 0)
        return rem_samples[rng_next(r) % COUNT(rem_samples)];
    return (int32_t)(rng_next(r) % KQT_TSTAMP_BEAT);
}


// The preconditions AddInRange and SubInRange from Tstamp64.lean. Outside
// them the C code has signed overflow, which is undefined behaviour.
static bool add_in_range(int64_t b1, int64_t b2)
{
    const __int128 s = (__int128)b1 + b2;
    return (s > (__int128)INT64_MIN) && (s < (__int128)INT64_MAX);
}

static bool sub_in_range(int64_t b1, int64_t b2)
{
    const __int128 d = (__int128)b1 - b2;
    return (d > (__int128)INT64_MIN) && (d < (__int128)INT64_MAX);
}


typedef struct
{
    uint64_t seed;
    long checked;
    long skipped;
    long mismatches;
} Thread_result;


static void report(const char* op, int64_t b1, int32_t r1, int64_t b2, int32_t r2)
{
    fprintf(stderr, "mismatch in %s: (%" PRId64 ", %" PRId32 "), (%" PRId64 ", %" PRId32 ")\n",
            op, b1, r1, b2, r2);
}


static long check_case(int64_t b1, int32_t r1, int64_t b2, int32_t r2, long* skipped)
{
    long mismatches = 0;
    Tstamp a = { .beats = b1, .rem = r1 };
    Tstamp b = { .beats = b2, .rem = r2 };
    Tstamp res;

    const uint64_t lb1 = (uint64_t)b1, lb2 = (uint64_t)b2;
    const uint32_t lr1 = (uint32_t)r1, lr2 = (uint32_t)r2;

    if (add_in_range(b1, b2))
    {
        Tstamp_add(&res, &a, &b);
        if ((int64_t)kqt_lean_tstamp_add_beats(lb1, lr1, lb2, lr2) != res.beats ||
                (int32_t)kqt_lean_tstamp_add_rem(lb1, lr1, lb2, lr2) != res.rem)
        {
            report("add", b1, r1, b2, r2);
            ++mismatches;
        }
    }
    else
    {
        ++*skipped;
    }

    if (sub_in_range(b1, b2))
    {
        Tstamp_sub(&res, &a, &b);
        if ((int64_t)kqt_lean_tstamp_sub_beats(lb1, lr1, lb2, lr2) != res.beats ||
                (int32_t)kqt_lean_tstamp_sub_rem(lb1, lr1, lb2, lr2) != res.rem)
        {
            report("sub", b1, r1, b2, r2);
            ++mismatches;
        }
    }
    else
    {
        ++*skipped;
    }

    if ((int32_t)kqt_lean_tstamp_cmp(lb1, lr1, lb2, lr2) != Tstamp_cmp(&a, &b))
    {
        report("cmp", b1, r1, b2, r2);
        ++mismatches;
    }

    return mismatches;
}


static void* thread_main(void* arg)
{
    Thread_result* tr = arg;
    lean_initialize_thread();

    Rng rng = { tr->seed };

    for (long i = 0; i < RANDOM_CASES_PER_THREAD; ++i)
    {
        const int64_t b1 = random_beats(&rng);
        const int32_t r1 = random_rem(&rng);
        const int64_t b2 = random_beats(&rng);
        const int32_t r2 = random_rem(&rng);
        tr->mismatches += check_case(b1, r1, b2, r2, &tr->skipped);
        ++tr->checked;
    }

    // Arbitrary bit patterns, including invalid remainders. The C functions
    // would assert on these; the Lean functions must simply return.
    volatile uint64_t sink = 0;
    for (long i = 0; i < GARBAGE_CASES_PER_THREAD; ++i)
    {
        const uint64_t b1 = rng_next(&rng), b2 = rng_next(&rng);
        const uint32_t r1 = (uint32_t)rng_next(&rng), r2 = (uint32_t)rng_next(&rng);
        sink += kqt_lean_tstamp_add_beats(b1, r1, b2, r2);
        sink += kqt_lean_tstamp_add_rem(b1, r1, b2, r2);
        sink += kqt_lean_tstamp_sub_beats(b1, r1, b2, r2);
        sink += kqt_lean_tstamp_sub_rem(b1, r1, b2, r2);
        sink += kqt_lean_tstamp_cmp(b1, r1, b2, r2);
    }
    (void)sink;

    lean_finalize_thread();
    return NULL;
}


int main(void)
{
    lean_initialize_runtime_module();
    lean_object* res = initialize_kunquat_Kunquat(1);
    if (!lean_io_result_is_ok(res))
    {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 2;
    }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();

    // Exhaustive pairs of boundary values.
    long boundary_checked = 0, boundary_skipped = 0, boundary_mismatches = 0;
    for (int i1 = 0; i1 < COUNT(beat_samples); ++i1)
    for (int j1 = 0; j1 < COUNT(rem_samples); ++j1)
    for (int i2 = 0; i2 < COUNT(beat_samples); ++i2)
    for (int j2 = 0; j2 < COUNT(rem_samples); ++j2)
    {
        boundary_mismatches += check_case(
                beat_samples[i1], rem_samples[j1],
                beat_samples[i2], rem_samples[j2],
                &boundary_skipped);
        ++boundary_checked;
    }
    printf("boundary: %ld cases, %ld add/sub skipped (out of range), %ld mismatches\n",
            boundary_checked, boundary_skipped, boundary_mismatches);

    // Random cases on several threads at once.
    pthread_t threads[THREAD_COUNT];
    Thread_result results[THREAD_COUNT];
    for (int t = 0; t < THREAD_COUNT; ++t)
    {
        results[t] = (Thread_result){ .seed = 0x6b756e71756174ULL + (uint64_t)t };
        if (pthread_create(&threads[t], NULL, thread_main, &results[t]) != 0)
        {
            fprintf(stderr, "could not create thread %d\n", t);
            return 2;
        }
    }

    long checked = 0, skipped = 0, mismatches = boundary_mismatches;
    for (int t = 0; t < THREAD_COUNT; ++t)
    {
        pthread_join(threads[t], NULL);
        checked += results[t].checked;
        skipped += results[t].skipped;
        mismatches += results[t].mismatches;
    }
    printf("random: %ld cases on %d threads, %ld add/sub skipped (out of range)\n",
            checked, THREAD_COUNT, skipped);
    printf("garbage inputs: %ld calls, no crash\n",
            (long)THREAD_COUNT * GARBAGE_CASES_PER_THREAD * 5);
    printf("total mismatches: %ld\n", mismatches);

    return (mismatches == 0) ? 0 : 1;
}
