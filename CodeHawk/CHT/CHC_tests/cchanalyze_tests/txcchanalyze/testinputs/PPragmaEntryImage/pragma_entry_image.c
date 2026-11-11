#include <stdint.h>
#include <string.h>

#pragma pack(push, 1)
typedef struct
{
    uint8_t id;
    uint32_t comparison;
} Entry;
#pragma pack(pop)

uint32_t pragma_packed_image(const Entry *image)
{
    uint32_t value;
    memcpy(&value, &image[175].comparison, sizeof(value));
    return value;
}
