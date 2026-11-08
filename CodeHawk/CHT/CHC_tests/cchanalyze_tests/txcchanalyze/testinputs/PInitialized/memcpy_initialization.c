/* Isolate byte-copy initialization from LC's table and packet interfaces. */
#include <stdint.h>
#include <string.h>

typedef union
{
    uint32_t word;
    float real;
    unsigned char bytes[4];
} FourBytes;

uint32_t copy_scalar_good(void)
{
    uint32_t source = 42;
    uint32_t dest;
    memcpy(&dest, &source, sizeof(dest));
    return dest;
}

uint32_t copy_union_good(void)
{
    FourBytes source;
    FourBytes dest;
    source.word = 42;
    memcpy(&dest, &source, sizeof(dest));
    return dest.word;
}

float copy_float_good(void)
{
    FourBytes source;
    float dest;
    source.real = 1.0f;
    memcpy(&dest, &source, sizeof(dest));
    return dest;
}

uint32_t copy_scalar_bad(void)
{
    uint32_t source;
    uint32_t dest;
    /* Deliberate uninitialized source: negative analysis control only. */
    memcpy(&dest, &source, sizeof(dest));
    return dest;
}

uint32_t copy_partial_bad(void)
{
    uint32_t source = 42;
    uint32_t dest;
    /* Only one byte is initialized; reading the uint32 remains invalid. */
    memcpy(&dest, &source, 1);
    return dest;
}

void copy_bounds_bad(void)
{
    unsigned char source[4] = {1, 2, 3, 4};
    unsigned char dest[2];
    memcpy(dest, source, sizeof(source));
}
