/* Analysis-only controls for byte-range requirements with runtime counts. */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

extern int acquire(void **out, size_t size);
extern void require_bytes(const void *pointer, size_t count);
extern void require_words(const uint32_t *pointer, size_t count);
extern void release(void *pointer);
extern void opaque(void *pointer);

void full_clear(size_t size)
{
    void *raw, *view;
    if (size == 0 || acquire(&raw, size) < 0) return;
    view = raw;
    memset(view, 0, size);
    require_bytes(view, size);
}

void captured_count(size_t size)
{
    void *raw, *view;
    size_t count = size;
    if (count == 0 || acquire(&raw, count) < 0) return;
    view = raw;
    memset(view, 0, count);
    count = 0;
    require_bytes(view, size);
}

void bounded_prefix(size_t size, size_t prefix)
{
    void *raw, *view;
    if (size < 16 || prefix == 0 || prefix > 12 || acquire(&raw, size) < 0) return;
    view = raw;
    memset(view, 0, size);
    require_bytes((char *)view + 4, prefix);
}

void constant_clear(size_t count)
{
    void *raw, *view;
    if (count == 0 || count > 8 || acquire(&raw, 8) < 0) return;
    view = raw;
    memset(view, 0, 8);
    require_bytes(view, count);
}

void independent_counts(size_t size, size_t count)
{
    void *raw, *view;
    if (size == 0 || count == 0 || acquire(&raw, size) < 0) return;
    view = raw;
    memset(view, 0, size);
    require_bytes(view, count);
}

void changed_count(size_t size)
{
    void *raw, *view;
    if (size == 0 || size >= 8 || acquire(&raw, 16) < 0) return;
    view = raw;
    memset(view, 0, size);
    size = 8;
    require_bytes(view, size);
}

void short_branch(size_t size, int short_clear)
{
    void *raw, *view;
    if (size < 8 || acquire(&raw, size) < 0) return;
    view = raw;
    if (short_clear) memset(view, 0, 4);
    else memset(view, 0, size);
    require_bytes(view, size);
}

void expired_region(size_t size)
{
    void *raw, *view;
    if (size == 0 || acquire(&raw, size) < 0) return;
    view = raw;
    memset(view, 0, size);
    release(view);
    require_bytes(view, size);
}

void opaque_writer(size_t size)
{
    void *raw, *view;
    if (size == 0 || acquire(&raw, size) < 0) return;
    view = raw;
    memset(view, 0, size);
    opaque(view);
    require_bytes(view, size);
}

void wrapping_bound(size_t count)
{
    void *raw, *view;
    if (count + 1 > 8 || acquire(&raw, 8) < 0) return;
    view = raw;
    memset(view, 0, 8);
    require_bytes(view, count);
}

void signed_count(int count)
{
    void *raw, *view;
    if (acquire(&raw, 8) < 0) return;
    view = raw;
    memset(view, 0, 8);
    require_bytes(view, (size_t)count);
}

void word_count_is_not_bytes(size_t size)
{
    void *raw, *view;
    if (size == 0 || acquire(&raw, size) < 0) return;
    view = raw;
    memset(view, 0, size);
    require_words(view, size);
}
