/* Analysis-only: inferred byte requirements must remain caller obligations. */
#include <stdint.h>
#include <string.h>

extern void event(void);
extern const uint32_t *opaque_origin(void);

union word
{
    uint32_t bits;
    float value;
};

uint32_t scalar_copy(const uint32_t *source)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    return result;
}

float union_copy(const union word *source)
{
    float result;
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t read_before_event(const uint32_t *source)
{
    uint32_t result;
    uint32_t saved;
    memcpy(&result, source, sizeof(result));
    saved = result;
    event();
    return saved;
}

uint32_t event_after_copy(const uint32_t *source)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    event();
    return result;
}

uint32_t before_switch(const uint32_t *source, unsigned command)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    switch (command)
    {
        case 0: return result;
        default: event(); return 0;
    }
}

uint32_t formal_replaced_after(const uint32_t *source, const uint32_t *other)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    source = other;
    return result;
}

uint32_t event_before_copy(const uint32_t *source)
{
    uint32_t result;
    event();
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t formal_replaced_before(const uint32_t *source, const uint32_t *other)
{
    uint32_t result;
    source = other;
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t lost_origin(const uint32_t *source)
{
    uint32_t result;
    source = opaque_origin();
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t short_copy(const uint32_t *source)
{
    uint32_t result;
    memcpy(&result, source, 2);
    return result;
}

uint32_t narrow_source(const uint8_t *source)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t guarded_copy(const uint32_t *source, unsigned enabled)
{
    uint32_t result;
    if (!enabled) return 0;
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t nullable_copy(const uint32_t *source)
{
    uint32_t result;
    if (source == 0) return 0;
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t dirty_loop(const uint32_t *source, unsigned count)
{
    uint32_t result;
    do
    {
        memcpy(&result, source, sizeof(result));
        event();
    } while (count--);
    return result;
}

uint32_t dirty_backedge(const uint32_t *source, unsigned count)
{
    uint32_t result;
again:
    memcpy(&result, source, sizeof(result));
    event();
    if (count--) goto again;
    return result;
}

uint32_t overwrite_before_copy(uint32_t *source)
{
    uint32_t unknown;
    uint32_t result;
    memcpy(source, &unknown, sizeof(unknown));
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t authored_short(const uint32_t *source)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t initialized_caller(void)
{
    uint32_t source = 42;
    return scalar_copy(&source);
}

uint32_t uninitialized_caller(void)
{
    uint32_t source;
    return scalar_copy(&source);
}

uint32_t initialized_union_caller(void)
{
    union word source;
    source.bits = 0;
    return union_copy(&source) == 0.0f;
}

uint32_t uninitialized_union_caller(void)
{
    union word source;
    return union_copy(&source) == 0.0f;
}

uint32_t original_argument_caller(void)
{
    uint32_t source = 42;
    uint32_t other;
    return formal_replaced_after(&source, &other);
}
