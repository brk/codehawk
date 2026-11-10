/* Analysis-only controls for calls to same-file descriptor setters. */
#include <stddef.h>
#include <stdint.h>
#include <string.h>

struct descriptor
{
    void *address;
    size_t capacity;
    size_t content;
    uint32_t crc;
};

extern int acquire(void **out, size_t size);
extern void release(void *pointer);
extern void opaque(struct descriptor *state);
extern void external_setter(struct descriptor *state, void *pointer, size_t size);
extern void *get_pointer(const struct descriptor *state);
extern size_t get_capacity(const struct descriptor *state);
extern size_t get_content(const struct descriptor *state);
extern void require_bytes(const void *pointer, size_t count);

static inline void set_allocated(struct descriptor *state, void *pointer, size_t size)
{
    state->address = pointer;
    state->capacity = size;
    state->content = 0;
    state->crc = 0;
}

static inline void set_narrow(struct descriptor *state, void *pointer, size_t size)
{
    state->address = pointer;
    state->capacity = (uint16_t)size;
}

static inline void set_then_call(struct descriptor *state, void *pointer, size_t size)
{
    state->address = pointer;
    state->capacity = size;
    opaque(state);
}

void exact_extent(size_t size)
{
    struct descriptor state;
    void *raw, *view;
    size_t count;
    if (size < 8 || acquire(&raw, size) < 0) return;
    set_allocated(&state, raw, size);
    view = get_pointer(&state);
    count = get_capacity(&state);
    memset(view, 0, count);
    require_bytes(view, size);
}

uint32_t copy_after_setter(size_t size)
{
    struct descriptor state;
    void *raw, *view;
    size_t count;
    uint32_t value;
    if (size < 8 || acquire(&raw, size) < 0) return 0;
    set_allocated(&state, raw, size);
    view = get_pointer(&state);
    count = get_capacity(&state);
    memset(view, 0, count);
    memcpy(&value, (char *)view + 4, 4);
    return value;
}

void no_clear(size_t size)
{
    struct descriptor state;
    void *raw, *view;
    if (size < 8 || acquire(&raw, size) < 0) return;
    set_allocated(&state, raw, size);
    view = get_pointer(&state);
    require_bytes(view, size);
}

void cleared_logical_length(size_t size)
{
    struct descriptor state;
    void *raw, *view;
    size_t count;
    if (size < 8 || acquire(&raw, size) < 0) return;
    set_allocated(&state, raw, size);
    view = get_pointer(&state);
    count = get_content(&state);
    memset(view, 0, count);
    require_bytes(view, size);
}

void escaped_after_setter(size_t size)
{
    struct descriptor state;
    void *raw, *view;
    size_t count;
    if (size < 8 || acquire(&raw, size) < 0) return;
    set_allocated(&state, raw, size);
    opaque(&state);
    view = get_pointer(&state);
    count = get_capacity(&state);
    memset(view, 0, count);
    require_bytes(view, size);
}

void narrow_capacity(size_t size)
{
    struct descriptor state;
    void *raw, *view;
    size_t count;
    if (size < 8 || acquire(&raw, size) < 0) return;
    set_narrow(&state, raw, size);
    view = get_pointer(&state);
    count = get_capacity(&state);
    memset(view, 0, count);
    require_bytes(view, size);
}

void external_effect(size_t size)
{
    struct descriptor state;
    void *raw, *view;
    size_t count;
    if (size < 8 || acquire(&raw, size) < 0) return;
    external_setter(&state, raw, size);
    view = get_pointer(&state);
    count = get_capacity(&state);
    memset(view, 0, count);
    require_bytes(view, size);
}

void opaque_effect(size_t size)
{
    struct descriptor state;
    void *raw, *view;
    size_t count;
    if (size < 8 || acquire(&raw, size) < 0) return;
    set_then_call(&state, raw, size);
    view = get_pointer(&state);
    count = get_capacity(&state);
    memset(view, 0, count);
    require_bytes(view, size);
}

void released_region(size_t size)
{
    struct descriptor state;
    void *raw, *view;
    size_t count;
    if (size < 8 || acquire(&raw, size) < 0) return;
    set_allocated(&state, raw, size);
    view = get_pointer(&state);
    count = get_capacity(&state);
    memset(view, 0, count);
    release(view);
    require_bytes(view, size);
}

void second_region_without_clear(size_t size)
{
    struct descriptor state;
    void *first, *second, *view;
    if (size < 8 || acquire(&first, size) < 0) return;
    set_allocated(&state, first, size);
    view = get_pointer(&state);
    memset(view, 0, size);
    release(view);
    if (acquire(&second, size) < 0) return;
    set_allocated(&state, second, size);
    view = get_pointer(&state);
    require_bytes(view, size);
}
