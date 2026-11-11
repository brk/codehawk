/* Analysis-only copies from current global descriptor fields. */
#include <stdint.h>
#include <string.h>

union word { uint8_t u8; uint16_t u16; uint32_t u32; int8_t s8; int16_t s16; int32_t s32; float value; };
struct entry { uint32_t prefix[4]; union word comparison; uint32_t suffix[2]; };
struct descriptor { const struct entry *table; };
struct descriptor Global;
volatile struct descriptor VolatileGlobal;
extern void event(void);

uint32_t comparison(unsigned index, unsigned command)
{
    union word result;
    if (index >= 176) return 0;
    memcpy(&result, &Global.table[index].comparison, sizeof(result));
    switch (command)
    {
        case 0: return result.u8;
        case 1: return result.u16;
        case 2: return result.u32;
        case 3: return result.s8;
        case 4: return result.s16;
        case 5: return result.s32;
        default: return 0;
    }
}

uint32_t changed_global_before(unsigned index)
{
    uint32_t result;
    event();
    memcpy(&result, &Global.table[index].comparison, sizeof(result));
    return result;
}

uint32_t changed_global_after(unsigned index, const struct entry *other)
{
    uint32_t result;
    memcpy(&result, &Global.table[index].comparison, sizeof(result));
    Global.table = other;
    return result;
}

uint32_t event_after_copy(unsigned index)
{
    uint32_t result;
    memcpy(&result, &Global.table[index].comparison, sizeof(result));
    event();
    return result;
}

uint32_t short_copy(unsigned index)
{
    uint32_t result;
    memcpy(&result, &Global.table[index].comparison, 2);
    return result;
}

uint32_t volatile_source(unsigned index)
{
    uint32_t result;
    memcpy(&result, &VolatileGlobal.table[index].comparison, sizeof(result));
    return result;
}

struct tiny { uint8_t tag; };
const struct tiny *Tiny;
uint32_t narrow_source(unsigned index)
{
    uint32_t result;
    memcpy(&result, &Tiny[index].tag, sizeof(result));
    return result;
}

struct __attribute__((packed)) packed_entry { uint8_t pad; uint32_t value; };
const struct packed_entry *Packed;
uint32_t packed_source(unsigned index)
{
    uint32_t result;
    memcpy(&result, &Packed[index].value, sizeof(result));
    return result;
}

uintptr_t IntegerAddress;
uint32_t integer_address(unsigned index)
{
    uint32_t result;
    const struct entry *table = (const struct entry *)IntegerAddress;
    memcpy(&result, &table[index].comparison, sizeof(result));
    return result;
}

uint32_t two_images(const struct entry *other)
{
    uint32_t first, second, saved;
    memcpy(&first, &Global.table[0].comparison, 4);
    saved = first;
    Global.table = other;
    memcpy(&second, &Global.table[0].comparison, 4);
    return saved ^ second;
}
