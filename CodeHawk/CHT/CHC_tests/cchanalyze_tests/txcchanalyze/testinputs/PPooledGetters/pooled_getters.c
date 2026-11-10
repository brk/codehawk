/* Analysis only: invalid controls must never be executed. */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
typedef struct { void *pointer; size_t capacity; } Descriptor;
extern int acquire(void **out,size_t n);
extern void *read_pointer(const Descriptor *d);
extern size_t get_capacity(const Descriptor *d);
extern void release(void *p);
extern void opaque_descriptor(Descriptor *d);
extern void *root_identity(void *p);
#define START(N) void *raw; uint32_t *p,value; Descriptor d; if(acquire(&raw,(N))<0)return 0; p=raw; d.pointer=raw
uint32_t two_getters_good(void) { START(8); d.capacity=8; memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,p+1,4); return value; }
uint32_t pointer_getter_good(void) { START(8); d.capacity=8; memset(read_pointer(&d),0,8); memcpy(&value,p+1,4); return value; }
uint32_t size_getter_good(void) { START(8); d.capacity=8; memset(p,0,get_capacity(&d)); memcpy(&value,p+1,4); return value; }
uint32_t captured_getters_good(void) { START(8); d.capacity=8; size_t n=get_capacity(&d); void *q=read_pointer(&d); d.pointer=NULL; d.capacity=1; memset(q,0,n); memcpy(&value,p+1,4); return value; }
uint32_t zero_getter_bad(void) { START(8); d.capacity=0; memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,p+1,4); return value; }
uint32_t partial_getter_bad(void) { START(8); d.capacity=4; memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,p+1,4); return value; }
uint32_t oversized_getter_bad(void) { START(8); d.capacity=9; memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,p+1,4); return value; }
uint32_t released_getter_bad(void) { START(8); d.capacity=8; release(p); memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,p+1,4); return value; }
uint32_t opaque_getter_bad(void) { START(8); d.capacity=8; opaque_descriptor(&d); memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,p+1,4); return value; }
uint32_t escaped_getter_unknown(void) { START(8); d.capacity=8; Descriptor *other=root_identity(&d); memset(read_pointer(other),0,get_capacity(other)); memcpy(&value,p+1,4); return value; }
uint32_t missing_getter_bad(void) { START(8); memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,p+1,4); return value; }
uint32_t nested_getter_unknown(void) { uint32_t value; { void *raw; uint32_t *p; Descriptor d; if(acquire(&raw,8)<0)return 0; p=raw; d.pointer=raw; d.capacity=8; memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,p+1,4); } return value; }
uint32_t unguarded_getter_bad(void) { void *raw; uint32_t *p,value; Descriptor d; acquire(&raw,8); p=raw; d.pointer=raw; d.capacity=8; memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,p+1,4); return value; }
typedef struct { uint32_t prefix,comparison; } Entry;
uint32_t field_getters_good(void) { void *raw; Entry *p; uint32_t value; Descriptor d; if(acquire(&raw,16)<0)return 0; p=raw; d.pointer=raw; d.capacity=16; memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,&p[1].comparison,4); return value; }
uint32_t field_partial_bad(void) { void *raw; Entry *p; uint32_t value; Descriptor d; if(acquire(&raw,16)<0)return 0; p=raw; d.pointer=raw; d.capacity=12; memset(read_pointer(&d),0,get_capacity(&d)); memcpy(&value,&p[1].comparison,4); return value; }

uint32_t pointer_before_size_good(void)
{
    START(8);
    d.capacity = 8;
    void *view = read_pointer(&d);
    size_t length = get_capacity(&d);
    memset(view, 0, length);
    memcpy(&value, p + 1, 4);
    return value;
}

uint32_t pointer_before_short_size_bad(void)
{
    START(8);
    d.capacity = 8;
    void *view = read_pointer(&d);
    d.capacity = 4;
    size_t length = get_capacity(&d);
    memset(view, 0, length);
    memcpy(&value, p + 1, 4);
    return value;
}
