/*
 * Reads a song in the format used by JumpSim (see lean/JumpSim.lean), builds
 * it as a Kunquat module with one pattern instance per pattern length, plays
 * it with libkunquat and prints the playback time in beats.
 *
 * Usage: jump_play <audio buffer size> [max beats] < song.txt
 *
 * Exits with status 1 if playback has not stopped after max beats
 * (default 1000000), or if the player stops producing audio without stopping.
 */

#include <kunquat/Handle.h>
#include <kunquat/Player.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#define RATE 48000
#define FRAMES_PER_BEAT (RATE / 2) // default tempo 120
#define MAX_PATTERNS 16
#define MAX_TRIGGERS 256
#define ENTRY_SIZE 80


static kqt_Handle handle;

static int pattern_count = 0;
static int pattern_start[MAX_PATTERNS + 1]; // start times in beats

static char triggers[MAX_PATTERNS][MAX_TRIGGERS * ENTRY_SIZE];
static int trigger_count[MAX_PATTERNS];


static void set(const char* key, const char* data)
{
    if (!kqt_Handle_set_data(handle, key, data, (long)strlen(data)))
    {
        fprintf(stderr, "set_data %s: %s\n", key, kqt_Handle_get_error(handle));
        exit(2);
    }
}


// The pattern instance that plays at a time, and the row within it.
static int pattern_at(int time, int* row)
{
    for (int p = pattern_count - 1; p >= 0; --p)
    {
        if (time >= pattern_start[p])
        {
            *row = time - pattern_start[p];
            return p;
        }
    }
    fprintf(stderr, "bad time %d\n", time);
    exit(2);
}


static void add_trigger(int time, const char* event, const char* arg)
{
    int row = 0;
    const int p = pattern_at(time, &row);
    if (trigger_count[p] >= MAX_TRIGGERS)
    {
        fprintf(stderr, "too many triggers\n");
        exit(2);
    }

    char entry[ENTRY_SIZE] = "";
    snprintf(entry, sizeof(entry), "%s[[%d, 0], [\"%s\", %s]]",
            trigger_count[p] > 0 ? ", " : "", row, event, arg);
    strcat(triggers[p], entry);
    ++trigger_count[p];
}


int main(int argc, char** argv)
{
    const long buf_size = (argc > 1) ? atol(argv[1]) : 4096;
    const long long max_beats = (argc > 2) ? atoll(argv[2]) : 1000000;

    // Pattern lengths
    char line[1024] = "";
    if (fgets(line, sizeof(line), stdin) == NULL)
        return 2;
    pattern_start[0] = 0;
    for (char* tok = strtok(line, " \n"); tok != NULL; tok = strtok(NULL, " \n"))
    {
        const int len = atoi(tok);
        if (len <= 0 || pattern_count >= MAX_PATTERNS)
        {
            fprintf(stderr, "bad pattern length\n");
            return 2;
        }
        pattern_start[pattern_count + 1] = pattern_start[pattern_count] + len;
        ++pattern_count;
    }
    if (pattern_count == 0)
        return 2;

    // Triggers
    int time = 0;
    char kind[8] = "";
    while (scanf("%d %7s", &time, kind) == 2)
    {
        if (time < 0 || time >= pattern_start[pattern_count])
        {
            fprintf(stderr, "bad time %d\n", time);
            return 2;
        }

        int arg = 0;
        char value[48] = "";
        if (strcmp(kind, "mj") == 0)
        {
            add_trigger(time, "mj", "null");
        }
        else if (strcmp(kind, "jc") == 0 && scanf("%d", &arg) == 1)
        {
            snprintf(value, sizeof(value), "\"%d\"", arg);
            add_trigger(time, "m.jc", value);
        }
        else if (strcmp(kind, "jr") == 0 && scanf("%d", &arg) == 1)
        {
            snprintf(value, sizeof(value), "\"ts(%d, 0)\"", arg);
            add_trigger(time, "m.jr", value);
        }
        else if (strcmp(kind, "jt") == 0 && scanf("%d", &arg) == 1)
        {
            int row = 0;
            const int target = pattern_at(arg, &row);
            snprintf(value, sizeof(value), "\"pat(%d, 0)\"", target);
            add_trigger(time, "m.jp", value);
            snprintf(value, sizeof(value), "\"ts(%d, 0)\"", row);
            add_trigger(time, "m.jr", value);
        }
        else
        {
            fprintf(stderr, "bad trigger line\n");
            return 2;
        }
    }

    handle = kqt_new_Handle();
    if (!handle)
        return 2;

    char order_list[MAX_PATTERNS * 32] = "[0, [";
    for (int p = 0; p < pattern_count; ++p)
    {
        char entry[32] = "";
        snprintf(entry, sizeof(entry), "%s[%d, 0]", p > 0 ? ", " : "", p);
        strcat(order_list, entry);
    }
    strcat(order_list, "]]");

    set("album/p_manifest.json", "[0, {}]");
    set("album/p_tracks.json", "[0, [0]]");
    set("song_00/p_manifest.json", "[0, {}]");
    set("song_00/p_order_list.json", order_list);

    for (int p = 0; p < pattern_count; ++p)
    {
        char key[64] = "";
        char data[MAX_TRIGGERS * ENTRY_SIZE + 16] = "";

        snprintf(key, sizeof(key), "pat_%03d/p_manifest.json", p);
        set(key, "[0, {}]");
        snprintf(key, sizeof(key), "pat_%03d/p_length.json", p);
        snprintf(data, sizeof(data), "[0, [%d, 0]]",
                pattern_start[p + 1] - pattern_start[p]);
        set(key, data);
        snprintf(key, sizeof(key), "pat_%03d/instance_000/p_manifest.json", p);
        set(key, "[0, {}]");
        if (trigger_count[p] > 0)
        {
            snprintf(key, sizeof(key), "pat_%03d/col_00/p_triggers.json", p);
            snprintf(data, sizeof(data), "[0, [%s]]", triggers[p]);
            set(key, data);
        }
    }

    if (!kqt_Handle_validate(handle))
    {
        fprintf(stderr, "validate: %s\n", kqt_Handle_get_error(handle));
        return 2;
    }
    kqt_Handle_set_audio_rate(handle, RATE);
    kqt_Handle_set_audio_buffer_size(handle, buf_size);

    const long long max_frames = (long long)FRAMES_PER_BEAT * max_beats;
    long long total = 0;
    int idle_calls = 0;
    while (!kqt_Handle_has_stopped(handle) && total < max_frames)
    {
        kqt_Handle_play(handle, buf_size);
        const long frames = kqt_Handle_get_frames_available(handle);
        total += frames;
        idle_calls = (frames == 0) ? idle_calls + 1 : 0;
        if (idle_calls > 100000)
        {
            fprintf(stderr, "stalled: no audio and not stopped after %lld frames\n",
                    total);
            return 1;
        }
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
