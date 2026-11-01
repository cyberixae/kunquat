/*
 * Regression test for a crash in the jump handling of the C player, fixed in
 * src/lib/player/Player_seq.c.
 *
 * Song: pattern instance P0 (1 beat, no triggers), then P1 (1 beat) with
 * [m.jc 1] [m.jp pat(0, 0)] [mj] on row 0. By the specification it plays
 * P0, P1, jumps back once, plays P0, P1 again and stops: 3 beats, 1.5 s at the
 * default tempo. The jump model in lean/Kunquat/Jump.lean agrees (`crashSong`).
 *
 * Before the fix, the player aborted with some audio buffer sizes:
 *
 *   AAtree.c: AAtree_attach: Assertion `diff != 0' failed.
 *
 * Player_process_cgiters looked up the next jump context once per render
 * slice, within the current pattern instance. When a slice started at the end
 * of P0 and continued into P1, the context left at P1 row 0 by the first jump
 * was not found, so the mj trigger was processed again and a second context
 * with the same key was added. rassert is enabled in all builds, so this
 * aborted release builds too.
 *
 * Each buffer size is played in a child process so that an abort is reported
 * instead of ending the test. Exits non-zero if any size fails.
 */

#include <kunquat/Handle.h>
#include <kunquat/Player.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>


#define RATE 48000


static kqt_Handle handle;


static void set(const char* key, const char* data)
{
    if (!kqt_Handle_set_data(handle, key, data, (long)strlen(data)))
    {
        fprintf(stderr, "set_data %s: %s\n", key, kqt_Handle_get_error(handle));
        exit(2);
    }
}


// Returns the number of frames played, or -1 if playback did not stop.
static long play_song(long buf_size)
{
    handle = kqt_new_Handle();
    if (!handle)
        exit(2);

    set("album/p_manifest.json", "[0, {}]");
    set("album/p_tracks.json", "[0, [0]]");
    set("song_00/p_manifest.json", "[0, {}]");
    set("song_00/p_order_list.json", "[0, [ [0, 0], [1, 0] ]]");
    set("pat_000/p_manifest.json", "[0, {}]");
    set("pat_000/p_length.json", "[0, [1, 0]]");
    set("pat_000/instance_000/p_manifest.json", "[0, {}]");
    set("pat_001/p_manifest.json", "[0, {}]");
    set("pat_001/p_length.json", "[0, [1, 0]]");
    set("pat_001/instance_000/p_manifest.json", "[0, {}]");
    set("pat_001/col_00/p_triggers.json",
            "[0, [ [[0, 0], [\"m.jc\", \"1\"]],"
            "      [[0, 0], [\"m.jp\", \"pat(0, 0)\"]],"
            "      [[0, 0], [\"mj\", null]] ]]");

    if (!kqt_Handle_validate(handle))
    {
        fprintf(stderr, "validate: %s\n", kqt_Handle_get_error(handle));
        exit(2);
    }
    kqt_Handle_set_audio_rate(handle, RATE);
    kqt_Handle_set_audio_buffer_size(handle, buf_size);

    long total = 0;
    while (!kqt_Handle_has_stopped(handle))
    {
        if (total > RATE * 60)
            return -1;
        kqt_Handle_play(handle, buf_size);
        total += kqt_Handle_get_frames_available(handle);
    }

    kqt_del_Handle(handle);
    return total;
}


int main(void)
{
    static const long sizes[] =
        { 64, 256, 1000, 1024, 3000, 4000, 4096, 8000, 8192, 12000, 24000, 32768, 48000 };
    const long expected = RATE * 3 / 2;
    int failures = 0;

    for (size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i)
    {
        fflush(stdout);
        const pid_t pid = fork();
        if (pid == 0)
        {
            // Silence the assertion backtrace; the parent reports the result.
            if (freopen("/dev/null", "w", stderr) == NULL)
                _exit(2);
            const long frames = play_song(sizes[i]);
            _exit(frames == expected ? 0 : 1);
        }

        int status = 0;
        waitpid(pid, &status, 0);
        if (WIFEXITED(status) && WEXITSTATUS(status) == 0)
        {
            printf("buffer %6ld: ok\n", sizes[i]);
        }
        else
        {
            ++failures;
            if (WIFSIGNALED(status))
                printf("buffer %6ld: FAILED (signal %d)\n", sizes[i], WTERMSIG(status));
            else
                printf("buffer %6ld: FAILED (wrong length)\n", sizes[i]);
        }
    }

    printf("%d of %zu buffer sizes failed\n", failures, sizeof(sizes) / sizeof(sizes[0]));
    return failures == 0 ? 0 : 1;
}
