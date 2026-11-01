/*
 * Reads a module description in the format used by SeqSim (see
 * lean/SeqSim.lean), builds the module, plays it with libkunquat and prints
 * the events the player reports.
 *
 * Output: for each play call that reports events, a line
 *   call <first frame> <frames rendered> <JSON list of events>
 * and at the end
 *   end <total frames>
 *
 * Usage: seq_play <frames per play call> [max frames] < module.txt
 * Exits with status 1 if playback has not stopped after max frames (default
 * 10000000) or the player stops producing audio without stopping.
 */

#include <kunquat/Handle.h>
#include <kunquat/Player.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


#define RATE 4800
#define QUARTER_REM (882161280 / 4)
#define MAX_PATTERNS 32
#define MAX_COLUMNS 8
#define COLUMN_DATA_SIZE 16384


static kqt_Handle handle;

static int pattern_len[MAX_PATTERNS];
static int pattern_used[MAX_PATTERNS];
static char columns[MAX_PATTERNS][MAX_COLUMNS][COLUMN_DATA_SIZE];
static int column_count[MAX_PATTERNS][MAX_COLUMNS];


static void set(const char* key, const char* data)
{
    if (!kqt_Handle_set_data(handle, key, data, (long)strlen(data)))
    {
        fprintf(stderr, "set_data %s: %s\n", key, kqt_Handle_get_error(handle));
        exit(2);
    }
}


static void bad_input(const char* line)
{
    fprintf(stderr, "bad input line: %s", line);
    exit(2);
}


int main(int argc, char** argv)
{
    const long chunk = (argc > 1) ? atol(argv[1]) : 1;
    const long long max_frames = (argc > 2) ? atoll(argv[2]) : 10000000;
    if (chunk <= 0)
        return 2;

    handle = kqt_new_Handle();
    if (!handle)
        return 2;

    char order_list[1024] = "[0, [";
    char line[256] = "";
    while (fgets(line, sizeof(line), stdin) != NULL)
    {
        char word[16] = "";
        int pos = 0;
        if (sscanf(line, "%15s%n", word, &pos) != 1)
            continue;

        if (strcmp(word, "order") == 0)
        {
            const char* p = line + pos;
            int pat = 0;
            int n = 0;
            int count = 0;
            while (sscanf(p, "%d%n", &pat, &n) == 1)
            {
                if (pat < 0 || pat >= MAX_PATTERNS)
                    bad_input(line);
                char entry[32] = "";
                snprintf(entry, sizeof(entry), "%s[%d, 0]", count > 0 ? ", " : "", pat);
                strcat(order_list, entry);
                p += n;
                ++count;
            }
        }
        else if (strcmp(word, "pattern") == 0)
        {
            int pat = 0;
            int len = 0;
            if (sscanf(line + pos, "%d %d", &pat, &len) != 2 ||
                    pat < 0 || pat >= MAX_PATTERNS || len < 0)
                bad_input(line);
            pattern_len[pat] = len;
            pattern_used[pat] = 1;
        }
        else if (strcmp(word, "trig") == 0)
        {
            int pat = 0;
            int col = 0;
            int row = 0;
            char ev[8] = "";
            int arg = 0;
            const int n = sscanf(line + pos, "%d %d %d %7s %d", &pat, &col, &row, ev, &arg);
            if (n < 4 || pat < 0 || pat >= MAX_PATTERNS || col < 0 || col >= MAX_COLUMNS)
                bad_input(line);

            char arg_json[48] = "null";
            if (strcmp(ev, "mj") == 0)
                ;
            else if (n < 5)
                bad_input(line);
            else if (strcmp(ev, "m.jp") == 0)
                snprintf(arg_json, sizeof(arg_json), "\"pat(%d, 0)\"", arg);
            else if (strcmp(ev, "m.jr") == 0)
                snprintf(arg_json, sizeof(arg_json), "\"ts(%d, %d)\"",
                        arg / 4, (arg % 4) * QUARTER_REM);
            else
                snprintf(arg_json, sizeof(arg_json), "\"%d\"", arg);

            char entry[128] = "";
            snprintf(entry, sizeof(entry), "%s[[%d, %d], [\"%s\", %s]]",
                    column_count[pat][col] > 0 ? ", " : "",
                    row / 4, (row % 4) * QUARTER_REM, ev, arg_json);
            if (strlen(columns[pat][col]) + strlen(entry) + 1 > COLUMN_DATA_SIZE)
                bad_input(line);
            strcat(columns[pat][col], entry);
            ++column_count[pat][col];
        }
        else
        {
            bad_input(line);
        }
    }
    strcat(order_list, "]]");

    set("album/p_manifest.json", "[0, {}]");
    set("album/p_tracks.json", "[0, [0]]");
    set("song_00/p_manifest.json", "[0, {}]");
    set("song_00/p_order_list.json", order_list);

    for (int p = 0; p < MAX_PATTERNS; ++p)
    {
        if (!pattern_used[p])
            continue;

        char key[64] = "";
        static char data[COLUMN_DATA_SIZE + 16];

        snprintf(key, sizeof(key), "pat_%03d/p_manifest.json", p);
        set(key, "[0, {}]");
        snprintf(key, sizeof(key), "pat_%03d/p_length.json", p);
        snprintf(data, sizeof(data), "[0, [%d, %d]]",
                pattern_len[p] / 4, (pattern_len[p] % 4) * QUARTER_REM);
        set(key, data);
        snprintf(key, sizeof(key), "pat_%03d/instance_000/p_manifest.json", p);
        set(key, "[0, {}]");

        for (int c = 0; c < MAX_COLUMNS; ++c)
        {
            if (column_count[p][c] == 0)
                continue;
            snprintf(key, sizeof(key), "pat_%03d/col_%02d/p_triggers.json", p, c);
            snprintf(data, sizeof(data), "[0, [%s]]", columns[p][c]);
            set(key, data);
        }
    }

    if (!kqt_Handle_validate(handle))
    {
        fprintf(stderr, "validate: %s\n", kqt_Handle_get_error(handle));
        return 2;
    }
    kqt_Handle_set_audio_rate(handle, RATE);
    if (chunk > kqt_Handle_get_audio_buffer_size(handle))
        kqt_Handle_set_audio_buffer_size(handle, chunk);

    long long total = 0;
    int idle_calls = 0;
    while (!kqt_Handle_has_stopped(handle))
    {
        if (total >= max_frames)
        {
            fprintf(stderr, "did not stop\n");
            return 1;
        }

        kqt_Handle_play(handle, chunk);
        const long frames = kqt_Handle_get_frames_available(handle);

        for (;;)
        {
            const char* events = kqt_Handle_receive_events(handle);
            if (events == NULL)
            {
                fprintf(stderr, "receive_events: %s\n", kqt_Handle_get_error(handle));
                return 2;
            }
            if (strcmp(events, "[]") == 0)
                break;
            printf("call %lld %ld %s\n", total, frames, events);
        }

        total += frames;
        idle_calls = (frames == 0) ? idle_calls + 1 : 0;
        if (idle_calls > 100000)
        {
            fprintf(stderr, "stalled: no audio and not stopped after %lld frames\n", total);
            return 1;
        }
    }

    printf("end %lld\n", total);
    kqt_del_Handle(handle);
    return 0;
}
