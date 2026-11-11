#include <stdint.h>
#include <string.h>

extern void event(void);
extern uint32_t contracted_copy(const uint32_t *source);

struct entry
{
    uint32_t prefix[4];
    uint32_t comparison;
    uint32_t suffix[2];
};

uint32_t pure_copy(const uint32_t *source)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t event_before_copy(const uint32_t *source)
{
    uint32_t result;
    event();
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t event_after_copy(const uint32_t *source)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    event();
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

uint32_t dirty_returning_path(const uint32_t *source, unsigned flag)
{
    uint32_t result;
    if (flag)
    {
        event();
        return 0;
    }
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t dirty_joining_path(const uint32_t *source, unsigned flag)
{
    uint32_t result;
    if (flag)
    {
        event();
    }
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t dirty_loop(const uint32_t *source, unsigned repeat)
{
    uint32_t result;
    do
    {
        memcpy(&result, source, sizeof(result));
        event();
    } while (repeat--);
    return result;
}

uint32_t dirty_backwards_goto(const uint32_t *source, unsigned repeat)
{
    uint32_t result;
again:
    memcpy(&result, source, sizeof(result));
    event();
    if (repeat--)
    {
        goto again;
    }
    return result;
}

uint32_t overwrite_source_before_copy(uint32_t *source)
{
    uint32_t unknown;
    uint32_t result;
    memcpy(source, &unknown, sizeof(unknown));
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t asm_after_copy(const uint32_t *source)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    __asm__ volatile ("" ::: "memory");
    return result;
}

uint32_t formal_replaced_before_copy(const uint32_t *source, const uint32_t *other)
{
    uint32_t result;
    source = other;
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t formal_replaced_after_copy(const uint32_t *source, const uint32_t *other)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    source = other;
    return result;
}

uint32_t initialized_caller(void)
{
    uint32_t source = 42;
    return read_before_event(&source);
}

uint32_t uninitialized_caller(void)
{
    uint32_t source;
    return read_before_event(&source);
}

uint32_t initialized_external_caller(void)
{
    uint32_t source = 42;
    return contracted_copy(&source);
}

uint32_t uninitialized_external_caller(void)
{
    uint32_t source;
    return contracted_copy(&source);
}

uint32_t bounded_field_before_event(const struct entry *source, unsigned index)
{
    uint32_t result;
    uint32_t saved;
    if (index >= 176)
    {
        return 0;
    }
    memcpy(&result, &source[index].comparison, sizeof(result));
    saved = result;
    index = UINT32_MAX;
    event();
    return saved;
}

uint32_t bounded_field_after_event(const struct entry *source, unsigned index)
{
    uint32_t result;
    if (index >= 176)
    {
        return 0;
    }
    event();
    memcpy(&result, &source[index].comparison, sizeof(result));
    return result;
}

uint32_t copy_before_switch(const uint32_t *source, unsigned command)
{
    uint32_t result;
    memcpy(&result, source, sizeof(result));
    switch (command)
    {
        case 0:
            return result;
        default:
            event();
            return 0;
    }
}

uint32_t dirty_switch_before_copy(const uint32_t *source, unsigned command)
{
    uint32_t result;
    switch (command)
    {
        case 0:
            event();
            break;
        default:
            break;
    }
    memcpy(&result, source, sizeof(result));
    return result;
}

uint32_t dirty_switch_fallthrough(const uint32_t *source, unsigned command)
{
    uint32_t result;
    switch (command)
    {
        case 0:
            event();
            /* fall through */
        case 1:
            memcpy(&result, source, sizeof(result));
            return result;
        default:
            return 0;
    }
}
