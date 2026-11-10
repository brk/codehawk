/* Analysis only: metadata values do not create region permission or contents. */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
typedef struct { void *pointer; size_t capacity; } Descriptor;
extern size_t get_capacity(const Descriptor *d);
extern size_t post_only_capacity(const Descriptor *d);
extern void opaque_descriptor(Descriptor *d);
extern void release(void *p);
uint32_t scalar_length_good(void) { uint32_t image[2],value; Descriptor d; d.capacity=sizeof(image); memset(image,0,get_capacity(&d)); memcpy(&value,image,4); return value; }
uint32_t scalar_captured_good(void) { uint32_t image[2],value; Descriptor d; size_t n; d.capacity=sizeof(image); n=get_capacity(&d); d.capacity=1; memset(image,0,n); memcpy(&value,image,4); return value; }
uint32_t scalar_heap_good(void) { uint32_t *p=malloc(8),value; Descriptor d; if(!p)return 0; d.capacity=8; memset(p,0,get_capacity(&d)); memcpy(&value,p,4); return value; }
uint32_t scalar_zero_bad(void) { uint32_t image[2],value; Descriptor d; d.capacity=0; memset(image,0,get_capacity(&d)); memcpy(&value,image,4); return value; }
uint32_t scalar_short_bad(void) { uint32_t image[2],value; Descriptor d; d.capacity=1; memset(image,0,get_capacity(&d)); memcpy(&value,image,4); return value; }
uint32_t scalar_oversized_bad(void) { uint32_t image[2],value; Descriptor d; d.capacity=9; memset(image,0,get_capacity(&d)); memcpy(&value,image,4); return value; }
uint32_t scalar_missing_bad(void) { uint32_t image[2],value; Descriptor d; memset(image,0,get_capacity(&d)); memcpy(&value,image,4); return value; }
uint32_t scalar_opaque_bad(void) { uint32_t image[2],value; Descriptor d; d.capacity=8; opaque_descriptor(&d); memset(image,0,get_capacity(&d)); memcpy(&value,image,4); return value; }
uint32_t scalar_post_only_unknown(void) { uint32_t image[2],value; Descriptor d; d.capacity=8; memset(image,0,post_only_capacity(&d)); memcpy(&value,image,4); return value; }
uint32_t scalar_union_unknown(void) { uint32_t image[2],value; union { Descriptor d; uint64_t raw[2]; } u; u.d.capacity=8; memset(image,0,get_capacity(&u.d)); memcpy(&value,image,4); return value; }
uint32_t scalar_volatile_unknown(void) { uint32_t image[2],value; volatile Descriptor d; d.capacity=8; memset(image,0,get_capacity((const Descriptor*)&d)); memcpy(&value,image,4); return value; }
uint32_t scalar_nested_unknown(void) { uint32_t image[2],value; { Descriptor d; d.capacity=8; memset(image,0,get_capacity(&d)); } memcpy(&value,image,4); return value; }
uint32_t scalar_released_bad(void) { uint32_t *p=malloc(8),value; Descriptor d; if(!p)return 0; d.capacity=8; release(p); memset(p,0,get_capacity(&d)); memcpy(&value,p,4); return value; }
typedef struct { double capacity; } FloatDescriptor;
extern double get_float_capacity(const FloatDescriptor *d);
uint32_t scalar_float_unknown(void) { uint32_t image[2],value; FloatDescriptor d; d.capacity=8.0; memset(image,0,(size_t)get_float_capacity(&d)); memcpy(&value,image,4); return value; }
#include <stdbool.h>
typedef struct { bool capacity; } BoolDescriptor;
extern bool get_bool_capacity(const BoolDescriptor *d);
uint32_t scalar_bool_bad(void) { uint32_t image[2],value; BoolDescriptor d; d.capacity=true; memset(image,0,get_bool_capacity(&d)); memcpy(&value,image,4); return value; }
