#include <stdint.h>
#include <string.h>
union word { uint32_t bits; float value; };
struct entry { uint32_t prefix[4]; union word comparison; uint32_t suffix[2]; };
const struct entry *Table;
extern uint32_t consume(union word *value);
extern void publish(union word *value);
extern void event(void);

uint32_t straight(unsigned index)
{
    union word value;
    memcpy(&value, &Table[index].comparison, 4);
    return consume(&value);
}

uint32_t clean_break(unsigned command)
{
    union word value;
    memcpy(&value, &Table[0].comparison, 4);
    switch (command)
    {
        case 0: event(); break;
        case 1: return consume(&value);
        default: return 0;
    }
    return 0;
}

uint32_t dirty_fallthrough(unsigned command)
{
    union word value;
    memcpy(&value, &Table[0].comparison, 4);
    switch (command)
    {
        case 0: event();
        case 1: return consume(&value);
        default: return 0;
    }
}

uint32_t event_before_copy(void)
{
    union word value;
    event();
    memcpy(&value, &Table[0].comparison, 4);
    return consume(&value);
}

uint32_t event_after_copy(void)
{
    union word value;
    memcpy(&value, &Table[0].comparison, 4);
    event();
    return consume(&value);
}

uint32_t escaped_before_copy(void)
{
    union word value;
    publish(&value);
    memcpy(&value, &Table[0].comparison, 4);
    return consume(&value);
}

uint32_t short_copy(void)
{
    union word value;
    memcpy(&value, &Table[0].comparison, 2);
    return consume(&value);
}

uint32_t guarded_copy(unsigned enabled)
{
    union word value;
    if (enabled) memcpy(&value, &Table[0].comparison, 4);
    return consume(&value);
}

uint32_t dirty_overwrite(void)
{
    union word value;
    uint8_t unknown;
    memcpy(&value, &Table[0].comparison, 4);
    memcpy(&value, &unknown, 1);
    return consume(&value);
}

uint32_t returning_path(unsigned enabled)
{
    union word value;
    if (enabled) return 0;
    memcpy(&value, &Table[0].comparison, 4);
    return consume(&value);
}

uint32_t copy_in_branch(unsigned enabled)
{
    union word value;
    if (enabled) memcpy(&value, &Table[0].comparison, 4);
    else return 0;
    return consume(&value);
}

uint32_t replaced_image(const struct entry *other)
{
    union word value;
    memcpy(&value, &Table[0].comparison, 4);
    Table = other;
    return consume(&value);
}

uint32_t second_image(const struct entry *other)
{
    union word value;
    memcpy(&value, &Table[0].comparison, 4);
    Table = other;
    memcpy(&value, &Table[0].comparison, 4);
    return consume(&value);
}

uint32_t loop_copy(unsigned repeat)
{
    union word value;
    do { memcpy(&value, &Table[0].comparison, 4); } while (repeat--);
    return consume(&value);
}

uint32_t goto_copy(void)
{
    union word value;
    memcpy(&value, &Table[0].comparison, 4);
    goto done;
done:
    return consume(&value);
}

uint32_t asm_copy(void)
{
    union word value;
    memcpy(&value, &Table[0].comparison, 4);
    __asm__ volatile ("" ::: "memory");
    return consume(&value);
}

uint32_t nested_copy(void)
{
    {
        union word value;
        memcpy(&value, &Table[0].comparison, 4);
        return consume(&value);
    }
}

void *Escaped;
uint32_t captured_return(void)
{
    union word value;
    Escaped = memcpy(&value, &Table[0].comparison, 4);
    return consume(&value);
}
