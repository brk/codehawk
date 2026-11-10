/* Analysis-only controls for byte counts at allocation and clear calls. */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

extern int acquire(void **out, size_t size);
extern void release(void *pointer);
extern void update_size(size_t *size);

uint32_t same_parameter(size_t size)
{
    void *raw;
    uint32_t *view, value;
    if (size < 8 || acquire(&raw, size) < 0) return 0;
    view = raw;
    memset(view, 0, size);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t constant_slot(void)
{
    size_t size = 8;
    void *raw;
    uint32_t *view, value;
    if (acquire(&raw, size) < 0) return 0;
    view = raw;
    memset(view, 0, size);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t bounded_prefix(size_t size)
{
    void *raw;
    uint32_t *view, value;
    if (size < 16 || acquire(&raw, size) < 0) return 0;
    view = raw;
    memset(view, 0, 8);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t smaller_clear(void)
{
    size_t size = 16;
    void *raw;
    uint32_t *view, value;
    if (acquire(&raw, size) < 0) return 0;
    view = raw;
    size = 8;
    memset(view, 0, size);
    size = 0;
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t overwrite_count_after_clear(size_t size)
{
    void *raw;
    uint32_t *view, value;
    if (size < 8 || acquire(&raw, size) < 0) return 0;
    view = raw;
    memset(view, 0, size);
    size = 0;
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t different_counts(size_t capacity, size_t length)
{
    void *raw;
    uint32_t *view, value;
    if (capacity < 8 || length < 8 || acquire(&raw, capacity) < 0) return 0;
    view = raw;
    memset(view, 0, length);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t larger_clear(void)
{
    size_t size = 8;
    void *raw;
    uint32_t *view, value;
    if (acquire(&raw, size) < 0) return 0;
    view = raw;
    size = 16;
    memset(view, 0, size);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t short_parameter(size_t size)
{
    void *raw;
    uint32_t *view, value;
    if (size < 4 || acquire(&raw, size) < 0) return 0;
    view = raw;
    memset(view, 0, size);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t release_before_clear(size_t size)
{
    void *raw;
    uint32_t *view, value;
    if (size < 8 || acquire(&raw, size) < 0) return 0;
    view = raw;
    release(view);
    memset(view, 0, size);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t inflate_after_short_clear(void)
{
    size_t size = 8;
    void *raw;
    uint32_t *view, value;
    if (acquire(&raw, size) < 0) return 0;
    view = raw;
    size = 4;
    memset(view, 0, size);
    size = 8;
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t signed_conversion(size_t capacity, int length)
{
    void *raw;
    uint32_t *view, value;
    if (capacity < 8 || acquire(&raw, capacity) < 0) return 0;
    view = raw;
    memset(view, 0, (size_t)length);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t mismatched_status(size_t size)
{
    void *raw, *other;
    uint32_t *view, value;
    if (size < 8) return 0;
    acquire(&raw, size);
    view = raw;
    if (acquire(&other, size) < 0) return 0;
    memset(view, 0, size);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t one_short_branch(size_t size, int short_clear)
{
    void *raw;
    uint32_t *view, value;
    if (size < 8 || acquire(&raw, size) < 0) return 0;
    view = raw;
    if (short_clear) memset(view, 0, 4);
    else memset(view, 0, size);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t addressed_count(size_t size)
{
    void *raw;
    uint32_t *view, value;
    update_size(&size);
    if (size < 8 || acquire(&raw, size) < 0) return 0;
    view = raw;
    memset(view, 0, size);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t wrapping_count(size_t size)
{
    void *raw;
    uint32_t *view, value;
    if (size < 8) return 0;
    size += 8;
    if (acquire(&raw, size) < 0) return 0;
    view = raw;
    memset(view, 0, size);
    memcpy(&value, view + 1, 4);
    return value;
}

uint32_t wrapping_guard(size_t size)
{
    void *raw;
    uint32_t *view, value;
    if (size - 1 < 7 || acquire(&raw, size) < 0) return 0;
    view = raw;
    memset(view, 0, size);
    memcpy(&value, view + 1, 4);
    return value;
}
