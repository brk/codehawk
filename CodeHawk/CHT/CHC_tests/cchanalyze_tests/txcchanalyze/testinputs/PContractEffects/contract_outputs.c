/* Contract regressions. Unsafe paths are analyzed, never executed. */
#include <stddef.h>
#include <string.h>

int optional_get(const int *source, int *out)
{
    if (!source || !out) return -1;
    *out = *source;
    return 0;
}

int initialized_output_good(void)
{
    int source = 42, out = 7;
    optional_get(&source, &out);
    return out;
}

int initialized_failure_good(void)
{
    int out = 7;
    optional_get(NULL, &out);
    return out;
}

int uninitialized_failure_bad(void)
{
    int out;
    optional_get(NULL, &out);
    return out;
}

int frame_good(void)
{
    int source = 42, out = 7, keep = 9;
    int *keep_address = &keep;
    (void)keep_address;
    optional_get(&source, &out);
    return keep;
}

void unknown_output(int *out)
{
    int uninitialized;
    memcpy(out, &uninitialized, sizeof(*out));
}

int block_write_invalidates_bad(void)
{
    int out = 7;
    unknown_output(&out);
    return out;
}

void two_outputs(int *first, int *second)
{
    *first = 99;
    *second = 99;
}

int two_outputs_first_bad(void)
{
    int first = 1, second = 1, array[8] = {0};
    two_outputs(&first, &second);
    return array[first];
}

int two_outputs_second_bad(void)
{
    int first = 1, second = 1, array[8] = {0};
    two_outputs(&first, &second);
    return array[second];
}

static int *escaped;

void post_only(int *out)
{
    int uninitialized;
    *out = 99;
    memcpy(escaped, &uninitialized, sizeof(*escaped));
}

int missing_footprint_bad(void)
{
    int out = 7, keep = 9;
    escaped = &keep;
    post_only(&out);
    return keep;
}
