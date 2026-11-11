#include <stdint.h>
#include <string.h>
union sample { uint8_t byte; uint16_t half; uint32_t word; float floating; };
unsigned Kind;
extern uint32_t consume(union sample *value);
extern uint32_t consume_word(uint32_t *value);
extern void event(void);

uint32_t cleared_union(void)
{
    union sample value;
    memset(&value, 0, sizeof(value));
    return consume(&value);
}

uint32_t scalar_word(uint32_t input)
{
    uint32_t value = input;
    return consume_word(&value);
}

uint32_t constant_member(void)
{
    union sample value;
    value.word = 42;
    return consume(&value);
}

uint32_t whole_member(uint32_t input)
{
    union sample value;
    value.word = input;
    return consume(&value);
}

uint32_t correlated_parameter(unsigned kind, uint32_t input)
{
    union sample value;
    switch (kind)
    {
        case 1: value.byte = input & 255; break;
        case 2: value.half = input & 65535; break;
        default: value.word = input; break;
    }
    switch (kind)
    {
        case 3: return consume(&value);
        default: return 0;
    }
}

uint32_t correlated_global(uint32_t input)
{
    union sample value;
    switch (Kind)
    {
        case 1: value.byte = input & 255; break;
        case 2: value.half = input & 65535; break;
        default: value.word = input; break;
    }
    switch (Kind)
    {
        case 3: return consume(&value);
        default: return 0;
    }
}

uint32_t changed_selector(uint32_t input)
{
    union sample value;
    switch (Kind)
    {
        case 1: value.byte = input & 255; break;
        case 2: value.half = input & 65535; break;
        default: value.word = input; break;
    }
    Kind = 3;
    return consume(&value);
}

uint32_t opaque_selector(uint32_t input)
{
    union sample value;
    switch (Kind)
    {
        case 1: value.byte = input & 255; break;
        case 2: value.half = input & 65535; break;
        default: value.word = input; break;
    }
    event();
    switch (Kind)
    {
        case 3: return consume(&value);
        default: return 0;
    }
}

uint32_t short_member(uint32_t input)
{
    union sample value;
    value.byte = input & 255;
    return consume(&value);
}

uint32_t uninitialized_member(void)
{
    union sample value;
    uint32_t unknown;
    value.word = unknown;
    return consume(&value);
}

uint32_t single_guard(unsigned kind, uint32_t input)
{
    union sample value;
    if (kind == 3)
    {
        value.word = input;
        return consume(&value);
    }
    return 0;
}

/* Expanded controls retain symbolic selectors, with no bounded input domain. */
#define WRITE_WIDTH(TAG) switch (TAG) { \
    case 1: value.byte = input & 255; break; \
    case 2: value.half = input & 65535; break; \
    default: value.word = input; break; }
#define FLOAT_CALL(TAG) switch (TAG) { case 3: return consume(&value); default: return 0; }

struct entry { unsigned kind; union sample comparison; };
const struct entry *Entries;
const volatile struct entry *VolatileEntries;
volatile unsigned VolatileKind;
union sample *Escaped;
extern void publish(union sample *value);
extern uint32_t consume_pair(union sample *first, union sample *second);

uint32_t descriptor_copy(unsigned index, uint32_t input)
{
    union sample value, other;
    WRITE_WIDTH(Entries[index].kind)
    memcpy(&other, &Entries[index].comparison, 4);
    switch (Entries[index].kind)
    {
        case 3: return consume_pair(&value, &other);
        default: return 0;
    }
}

uint32_t multiple_query_cases(unsigned kind, uint32_t input)
{
    union sample value;
    WRITE_WIDTH(kind)
    switch (kind) { case 3: case 4: return consume(&value); default: return 0; }
}

uint32_t first_fallthrough_full(unsigned kind, uint32_t input)
{
    union sample value;
    switch (kind)
    {
        case 1: value.byte = input & 255; break;
        case 2: value.half = input & 65535; break;
        case 3: value.byte = input & 255;
        default: value.word = input; break;
    }
    FLOAT_CALL(kind)
}

uint32_t constant_default(unsigned kind, uint32_t input)
{
    union sample value;
    switch (kind) { case 1: value.byte = input & 255; break; default: value.word = 42; break; }
    FLOAT_CALL(kind)
}

uint32_t dirty_query_fallthrough(unsigned kind, uint32_t input)
{
    union sample value;
    WRITE_WIDTH(kind)
    switch (kind) { case 1: value.byte = 0; case 3: return consume(&value); default: return 0; }
}

uint32_t merged_query_labels(unsigned kind, uint32_t input)
{
    union sample value;
    WRITE_WIDTH(kind)
    switch (kind) { case 1: case 3: return consume(&value); default: return 0; }
}

uint32_t wrong_case_width(unsigned kind, uint32_t input)
{
    union sample value;
    switch (kind) { case 3: value.byte = input & 255; break; default: value.word = input; break; }
    FLOAT_CALL(kind)
}

uint32_t changed_via_alias(uint32_t input)
{
    union sample value;
    unsigned *alias = &Kind;
    WRITE_WIDTH(Kind)
    *alias = 3;
    FLOAT_CALL(Kind)
}

uint32_t volatile_selector(uint32_t input)
{
    union sample value;
    WRITE_WIDTH(VolatileKind)
    FLOAT_CALL(VolatileKind)
}

uint32_t volatile_descriptor(unsigned index, uint32_t input)
{
    union sample value;
    WRITE_WIDTH(VolatileEntries[index].kind)
    FLOAT_CALL(VolatileEntries[index].kind)
}

uint32_t changed_index(unsigned index, uint32_t input)
{
    union sample value;
    WRITE_WIDTH(Entries[index].kind)
    index = 0;
    FLOAT_CALL(Entries[index].kind)
}

uint32_t escaped_address(unsigned kind, uint32_t input)
{
    union sample value;
    publish(&value);
    WRITE_WIDTH(kind)
    FLOAT_CALL(kind)
}

uint32_t stored_address(unsigned kind, uint32_t input)
{
    union sample value;
    Escaped = &value;
    WRITE_WIDTH(kind)
    FLOAT_CALL(kind)
}

uint32_t partial_overwrite(unsigned kind, uint32_t input)
{
    union sample value;
    uint8_t unknown;
    WRITE_WIDTH(kind)
    memcpy(&value, &unknown, 1);
    FLOAT_CALL(kind)
}

uint32_t uninitialized_switch_word(unsigned kind, uint32_t input)
{
    union sample value;
    uint32_t unknown;
    switch (kind) { case 1: value.byte = input & 255; break; default: value.word = unknown; break; }
    FLOAT_CALL(kind)
}

uint32_t opaque_before_reads(unsigned kind, uint32_t input)
{
    union sample value;
    event();
    WRITE_WIDTH(kind)
    FLOAT_CALL(kind)
}

uint32_t loop_selector(unsigned kind, uint32_t input)
{
    union sample value;
    do { WRITE_WIDTH(kind) } while (kind--);
    FLOAT_CALL(kind)
}

uint32_t goto_selector(unsigned kind, uint32_t input)
{
    union sample value;
    WRITE_WIDTH(kind)
    goto query;
query:
    FLOAT_CALL(kind)
}

uint32_t asm_selector(unsigned kind, uint32_t input)
{
    union sample value;
    WRITE_WIDTH(kind)
    __asm__ volatile ("" ::: "memory");
    FLOAT_CALL(kind)
}

uint32_t nested_result(unsigned kind, uint32_t input)
{
    {
        union sample value;
        WRITE_WIDTH(kind)
        FLOAT_CALL(kind)
    }
}

uint32_t case_range(unsigned kind, uint32_t input)
{
    union sample value;
    switch (kind) { case 1 ... 2: value.half = input & 65535; break; default: value.word = input; break; }
    FLOAT_CALL(kind)
}

uint32_t copied_selector(unsigned initial, uint32_t input)
{
    union sample value;
    unsigned kind;
    unsigned three = 3;
    memcpy(&kind, &initial, sizeof(kind));
    WRITE_WIDTH(kind)
    memcpy(&kind, &three, sizeof(kind));
    FLOAT_CALL(kind)
}

const struct entry *OtherEntries;
uint32_t copied_pointer_selector(uint32_t input)
{
    union sample value;
    const struct entry *cursor;
    memcpy(&cursor, &Entries, sizeof(cursor));
    WRITE_WIDTH(cursor->kind)
    memcpy(&cursor, &OtherEntries, sizeof(cursor));
    FLOAT_CALL(cursor->kind)
}

uint32_t caller_initialized(void)
{
    return correlated_parameter(3, 42);
}

uint32_t caller_uninitialized(void)
{
    uint32_t unknown;
    return correlated_parameter(3, unknown);
}

uint32_t converted_case_label(unsigned kind, uint32_t input)
{
    union sample value;
    switch (kind) { case -1: value.byte = input & 255; break; default: value.word = input; break; }
    switch (kind) { case UINT32_MAX: return consume(&value); default: return 0; }
}

uint32_t reverse_case_conversion(int kind, uint32_t input)
{
    union sample value;
    switch (kind) { case UINT32_MAX: value.byte = input & 255; break; default: value.word = input; break; }
    switch (kind) { case -1: return consume(&value); default: return 0; }
}
