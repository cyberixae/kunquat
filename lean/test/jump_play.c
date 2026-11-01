/*
 * Reads a song in the format used by JumpSim (see lean/JumpSim.lean), builds
 * it as a one-pattern Kunquat module, plays it with libkunquat and prints the
 * playback time in beats.
 *
 * Usage: jump_play <audio buffer size> < song.txt
 */

#include <kunquat/Handle.h>
#include <kunquat/Player.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#define RATE 48000
#define FRAMES_PER_BEAT (RATE / 2) // default tempo 120
#define MAX_SLOTS 256


static kqt_Handle handle;


static void set(const char* key, const char* data)
{
    if (!kqt_Handle_set_data(handle, key, data, (long)strlen(data)))
    {
        fprintf(stderr, "set_data %s: %s\n", key, kqt_Handle_get_error(handle));
        exit(2);
    }
}


int main(int argc, char** argv)
{
    const long buf_size = (argc > 1) ? atol(argv[1]) : 4096;

    int len = 0;
    if (scanf("%d", &len) != 1 || len <= 0)
    {
        fprintf(stderr, "bad length\n");
        return 2;
    }

    static char triggers[MAX_SLOTS * 64] = "[0, [";
    int count = 0;
    int row = 0;
    char kind[8] = "";
    while (scanf("%d %7s", &row, kind) == 2)
    {
        if (count >= MAX_SLOTS)
        {
            fprintf(stderr, "too many slots\n");
            return 2;
        }

        char entry[64] = "";
        int arg = 0;
        if (strcmp(kind, "mj") == 0)
            snprintf(entry, sizeof(entry), "[[%d, 0], [\"mj\", null]]", row);
        else if (strcmp(kind, "jc") == 0 && scanf("%d", &arg) == 1)
            snprintf(entry, sizeof(entry), "[[%d, 0], [\"m.jc\", \"%d\"]]", row, arg);
        else if (strcmp(kind, "jr") == 0 && scanf("%d", &arg) == 1)
            snprintf(entry, sizeof(entry), "[[%d, 0], [\"m.jr\", \"ts(%d, 0)\"]]", row, arg);
        else
        {
            fprintf(stderr, "bad slot\n");
            return 2;
        }

        if (count > 0)
            strcat(triggers, ", ");
        strcat(triggers, entry);
        ++count;
    }
    strcat(triggers, "]]");

    handle = kqt_new_Handle();
    if (!handle)
        return 2;

    char length[32] = "";
    snprintf(length, sizeof(length), "[0, [%d, 0]]", len);

    set("album/p_manifest.json", "[0, {}]");
    set("album/p_tracks.json", "[0, [0]]");
    set("song_00/p_manifest.json", "[0, {}]");
    set("song_00/p_order_list.json", "[0, [ [0, 0] ]]");
    set("pat_000/p_manifest.json", "[0, {}]");
    set("pat_000/p_length.json", length);
    set("pat_000/instance_000/p_manifest.json", "[0, {}]");
    set("pat_000/col_00/p_triggers.json", triggers);

    if (!kqt_Handle_validate(handle))
    {
        fprintf(stderr, "validate: %s\n", kqt_Handle_get_error(handle));
        return 2;
    }
    kqt_Handle_set_audio_rate(handle, RATE);
    kqt_Handle_set_audio_buffer_size(handle, buf_size);

    const long long max_frames = (long long)FRAMES_PER_BEAT * 1000000;
    long long total = 0;
    while (!kqt_Handle_has_stopped(handle) && total < max_frames)
    {
        kqt_Handle_play(handle, buf_size);
        total += kqt_Handle_get_frames_available(handle);
    }
    if (total >= max_frames)
    {
        fprintf(stderr, "did not stop\n");
        return 1;
    }
    if (total % FRAMES_PER_BEAT != 0)
    {
        fprintf(stderr, "not a whole number of beats: %lld frames\n", total);
        return 1;
    }

    printf("%lld\n", total / FRAMES_PER_BEAT);
    kqt_del_Handle(handle);
    return 0;
}
