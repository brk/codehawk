/* Contract consumer controls only. Unsafe cases are analyzed, never run. */
#include <stdint.h>
#include <string.h>

extern int CFE_TBL_GetAddress(void **out, int handle);
extern int CFE_TBL_ReleaseAddress(int handle);
extern int CFE_TBL_Manage(int handle);
extern void byte_span(uint32_t *ptr);
extern void index_span(uint32_t *ptr);

void *slot_good(void)
{
    void *table;
    CFE_TBL_GetAddress(&table, 1);
    return table;
}

void *field_slot_good(void)
{
    struct { int tag; void *table; } state;
    CFE_TBL_GetAddress(&state.table, 1);
    return state.table;
}

uint32_t *cast_slot_good(void)
{
    uint32_t *table;
    CFE_TBL_GetAddress((void *)&table, 1);
    return table;
}

void *failure_slot_good(void)
{
    void *table;
    if (CFE_TBL_GetAddress(&table, -1) != 0)
        return table;
    return 0;
}

void *sibling_slot_bad(void)
{
    struct { void *table, *sibling; } state;
    CFE_TBL_GetAddress(&state.table, 1);
    return state.sibling;
}

uint32_t pointee_bad(void)
{
    uint32_t *table;
    if (CFE_TBL_GetAddress((void *)&table, 1) == 0)
        return *table;
    return 0;
}

uint32_t extent_bad(void)
{
    uint32_t *table;
    if (CFE_TBL_GetAddress((void *)&table, 1) == 0)
        return table[176];
    return 0;
}

uint32_t copy_pointee_bad(void)
{
    void *table;
    uint32_t value = 0;
    if (CFE_TBL_GetAddress(&table, 1) == 0)
        memcpy(&value, table, sizeof(value));
    return value;
}

uint32_t released_bad(void)
{
    uint32_t *table;
    if (CFE_TBL_GetAddress((void *)&table, 1) == 0)
    {
        CFE_TBL_ReleaseAddress(1);
        CFE_TBL_Manage(1);
        return *table;
    }
    return 0;
}

uint32_t no_frame_bad(void)
{
    unsigned char image[4] = {1, 2, 3, 4};
    void *table;
    uint32_t value;
    CFE_TBL_GetAddress(&table, 1);
    memcpy(&value, image, sizeof(value));
    return value;
}

uint32_t slot_too_small_bad(void)
{
    uint32_t slot;
    CFE_TBL_GetAddress((void *)&slot, 1);
    return slot;
}

void explicit_bytes_good(void)
{
    uint32_t image[2] = {1, 2};
    byte_span(image);
}

void explicit_bytes_bad(void)
{
    uint32_t image = 1;
    byte_span(&image);
}

void explicit_indices_good(void)
{
    uint32_t image[2] = {1, 2};
    index_span(image);
}

void explicit_indices_bad(void)
{
    uint32_t image = 1;
    index_span(&image);
}

void *larger_stride_bad(void)
{
    uint32_t image[2] = {1, 2};
    return (uint64_t *)image + 2;
}

void *array_address_bad(void)
{
    uint32_t image[2] = {1, 2};
    return &image + 2;
}
