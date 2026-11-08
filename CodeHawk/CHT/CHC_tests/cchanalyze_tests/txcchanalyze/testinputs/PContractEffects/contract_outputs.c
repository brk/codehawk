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

typedef union { unsigned int full; unsigned char byte; } OutputUnion;
typedef struct { struct { unsigned int value; } inner; int untouched; } NestedOutput;

void union_field_output(OutputUnion *out) { out->full = 99; }
unsigned int union_field_good(void)
{
    OutputUnion out;
    union_field_output(&out);
    return out.full;
}

void union_byte_output(OutputUnion *out) { out->byte = 1; }
unsigned int union_wider_bad(void)
{
    OutputUnion out;
    union_byte_output(&out);
    return out.full;
}

void nested_field_output(NestedOutput *out) { out->inner.value = 99; }
unsigned int nested_field_good(void)
{
    NestedOutput out;
    nested_field_output(&out);
    return out.inner.value;
}
int nested_sibling_bad(void)
{
    NestedOutput out;
    nested_field_output(&out);
    return out.untouched;
}
