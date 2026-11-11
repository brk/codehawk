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

float copy_scalar_parameter(const float *source)
{
    float result;
    memcpy(&result, source, sizeof(result));
    return result;
}

union word
{
    uint32_t bits;
    float value;
};

float copy_union_parameter(const union word *source)
{
    float result;
    memcpy(&result, source, sizeof(result));
    return result;
}

float short_parameter_copy(const float *source)
{
    float result;
    memcpy(&result, source, 2);
    return result;
}

float narrow_parameter_copy(const uint8_t *source)
{
    float result;
    memcpy(&result, source, sizeof(result));
    return result;
}

extern const float *opaque_scalar(void);

float replaced_parameter(const float *source)
{
    float result;
    source = opaque_scalar();
    memcpy(&result, source, sizeof(result));
    return result;
}
