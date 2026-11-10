/* Analysis-only controls for exact initialized source requirements. */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

struct entry
{
    uint32_t comparison;
    uint8_t tag;
};

extern const struct entry *opaque_origin(void);

uint32_t copy_field(const struct entry *table, size_t index)
{
    uint32_t result;
    memcpy(&result, &table[index].comparison, sizeof(result));
    return result;
}

uint32_t copy_field_alias(const void *image, size_t index)
{
    const struct entry *table = image;
    uint32_t result;
    memcpy(&result, &table[index].comparison, sizeof(result));
    return result;
}

uint32_t short_copy(const struct entry *table)
{
    uint32_t result;
    memcpy(&result, &table[0].comparison, 2);
    return result;
}

uint32_t narrow_field(const struct entry *table)
{
    uint32_t result;
    memcpy(&result, &table[0].tag, sizeof(result));
    return result;
}

uint32_t lost_origin(const struct entry *table)
{
    uint32_t result;
    table = opaque_origin();
    memcpy(&result, &table[0].comparison, sizeof(result));
    return result;
}

uint32_t uninitialized_local(void)
{
    struct entry entry;
    uint32_t result;
    memcpy(&result, &entry.comparison, sizeof(result));
    return result;
}
