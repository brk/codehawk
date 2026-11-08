/* Analysis controls only: do not execute the deliberately invalid cases. */
#include <stdint.h>
#include <string.h>

uint32_t copy_then_change_good(void)
{
    uint32_t source = 42, dest;
    memcpy(&dest, &source, sizeof(dest));
    source = 7;
    return dest;
}

uint32_t copy_then_initialize_bad(void)
{
    uint32_t source, dest;
    memcpy(&dest, &source, sizeof(dest));
    source = 42;
    return dest;
}

uint32_t copy_branch_good(int flag)
{
    uint32_t source, dest;
    if (flag)
        source = 42;
    else
        source = 7;
    memcpy(&dest, &source, sizeof(dest));
    return dest;
}

uint32_t copy_branch_bad(int flag)
{
    uint32_t source, dest;
    if (flag)
        source = 42;
    memcpy(&dest, &source, sizeof(dest));
    return dest;
}

uint32_t copy_zero_bad(void)
{
    uint32_t source = 42, dest;
    memcpy(&dest, &source, 0);
    return dest;
}

uint64_t copy_wider_bad(void)
{
    uint32_t source = 42;
    uint64_t dest;
    memcpy(&dest, &source, sizeof(source));
    return dest;
}

uint32_t copy_small_union_bad(void)
{
    union { uint16_t half; uint32_t word; } source;
    uint32_t dest;
    source.half = 42;
    memcpy(&dest, &source, sizeof(dest));
    return dest;
}

uint32_t copy_array_good(void)
{
    unsigned char source[4] = {1, 2, 3, 4};
    uint32_t dest;
    memcpy(&dest, source, sizeof(dest));
    return dest;
}

uint32_t copy_array_bad(void)
{
    unsigned char source[4];
    uint32_t dest;
    source[0] = 1;
    memcpy(&dest, source, sizeof(dest));
    return dest;
}

uint32_t copy_chain_bad(void)
{
    uint32_t source, middle, dest;
    memcpy(&middle, &source, sizeof(middle));
    memcpy(&dest, &middle, sizeof(dest));
    return dest;
}

uint32_t copy_local_count_good(void)
{
    uint32_t source = 42, dest;
    size_t count = sizeof(dest);
    memcpy(&dest, &source, count);
    count = 0;
    return dest;
}

uint32_t copy_late_count_bad(void)
{
    uint32_t source = 42, dest;
    size_t count = 1;
    memcpy(&dest, &source, count);
    count = sizeof(dest);
    return dest;
}

uint32_t copy_tail_field_bad(void)
{
    struct Pair { uint32_t first, second; } source = {1, 2}, dest;
    memcpy(&dest, &source, sizeof(source.first));
    return dest.second;
}

unsigned char copy_array_tail_bad(void)
{
    unsigned char source[4] = {1, 2, 3, 4}, dest[4];
    memcpy(dest, source, 1);
    return dest[3];
}

uint32_t copy_overwritten_array_bad(void)
{
    unsigned char source[4] = {1, 2, 3, 4}, unknown[4];
    uint32_t dest;
    memcpy(source, unknown, sizeof(source));
    memcpy(&dest, source, sizeof(dest));
    return dest;
}

extern void unknown_write(unsigned char *p);

uint32_t copy_unknown_write_bad(void)
{
    unsigned char source[4] = {1, 2, 3, 4};
    uint32_t dest;
    unknown_write(source);
    memcpy(&dest, source, sizeof(dest));
    return dest;
}

uint32_t copy_indirect_write_bad(void (*write_bytes)(unsigned char *))
{
    unsigned char source[4] = {1, 2, 3, 4};
    uint32_t dest;
    write_bytes(source);
    memcpy(&dest, source, sizeof(dest));
    return dest;
}
