#include <stddef.h>
#include <stdint.h>
#include <string.h>

typedef struct
{
    uint32_t id;
    uint32_t comparison;
} Entry;

typedef struct __attribute__((packed))
{
    uint8_t id;
    uint32_t comparison;
} PackedEntry;

extern void opaque(void);

uint32_t full_image(const Entry *image)
{
    uint32_t value;
    memcpy(&value, &image[175].comparison, sizeof(value));
    return value;
}

uint32_t bounded_image(const Entry *image, unsigned index)
{
    uint32_t value;
    if (index >= 176)
        return 0;
    memcpy(&value, &image[index].comparison, sizeof(value));
    return value;
}

uint32_t loop_image(const Entry *image)
{
    uint32_t value;
    uint32_t sum = 0;
    for (unsigned index = 0; index < 176; ++index)
    {
        memcpy(&value, &image[index].comparison, sizeof(value));
        sum ^= value;
    }
    return sum;
}

uint32_t prefix_field(const Entry *image)
{
    uint32_t value;
    memcpy(&value, &image[175].id, sizeof(value));
    return value;
}

uint32_t packed_image(const PackedEntry *image)
{
    uint32_t value;
    memcpy(&value, &image[175].comparison, sizeof(value));
    return value;
}

uint32_t short_image(const Entry *image)
{
    uint32_t value;
    memcpy(&value, &image[175].comparison, sizeof(value));
    return value;
}

uint32_t unbounded_image(const Entry *image, unsigned index)
{
    uint32_t value;
    memcpy(&value, &image[index].comparison, sizeof(value));
    return value;
}

uint32_t opaque_frame(const Entry *image)
{
    uint32_t value;
    opaque();
    memcpy(&value, &image[175].comparison, sizeof(value));
    return value;
}

uint32_t write_frame(const Entry *image, Entry *other)
{
    uint32_t value;
    other->comparison = 0;
    memcpy(&value, &image[175].comparison, sizeof(value));
    return value;
}

uint32_t replaced_base(const Entry *image, const Entry *other)
{
    uint32_t value;
    image = other;
    memcpy(&value, &image[175].comparison, sizeof(value));
    return value;
}

uint32_t checked_caller(void)
{
    Entry image[176];
    memset(image, 0, sizeof(image));
    return full_image(image);
}

uint32_t caller_without_initialization(void)
{
    Entry image[176];
    return full_image(image);
}
