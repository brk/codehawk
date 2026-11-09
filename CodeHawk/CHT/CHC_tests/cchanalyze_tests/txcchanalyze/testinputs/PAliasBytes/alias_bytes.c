/* Exact local alias controls. Unsafe functions are analyzed only, never run. */
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
typedef union { uint32_t bits; float floating; uint8_t bytes[4]; } Value;
typedef struct { uint8_t type, op; uint32_t mid, offset, mask; Value value; uint16_t count; } Entry;
typedef struct { void *pointer; size_t allocation; } Descriptor;
extern void opaque(void);
extern void readonly_call(void);
extern void overwrite(void *p);
extern void release(void *p);
extern void *identity(void *p);
uint32_t pointer_seed_good(void) { Entry a[176]; void *p=a; uint32_t value; memset(p,0,sizeof(a)); memcpy(&value,&a[175].value,4); return value; }
uint32_t descriptor_seed_good(void) { Entry a[176]; Descriptor d={a,sizeof(a)}; uint32_t value; memset(d.pointer,0,d.allocation); memcpy(&value,&a[175].value,4); return value; }
uint32_t pointer_source_good(void) { uint32_t a[2],value; void *p=a; memset(a,0,sizeof(a)); memcpy(&value,p,4); return value; }
uint32_t descriptor_source_good(void) { uint32_t a[2],value; Descriptor d={a,sizeof(a)}; memset(d.pointer,0,d.allocation); memcpy(&value,d.pointer,4); return value; }
uint32_t field_source_good(void) { Entry a[176]; Entry *p=a; uint32_t value; memset(p,0,sizeof(a)); memcpy(&value,&p[175].value,4); return value; }
uint32_t scalar_alias_good(void) { uint32_t a,value; uint32_t *p=&a; memset(p,0,sizeof(a)); memcpy(&value,p,4); return value; }
uint32_t byte_offset_good(void) { uint32_t a[2],value; unsigned char *p=(unsigned char*)a; memset(p+1,0,5); memcpy(&value,p+1,4); return value; }
uint32_t typed_offset_good(void) { uint32_t a[2],value; uint32_t *p=a; memset(a,0,sizeof(a)); memcpy(&value,p+1,4); return value; }
uint32_t short_count_bad(void) { uint32_t a[2],value; Descriptor d={a,1}; memset(d.pointer,0,d.allocation); memcpy(&value,d.pointer,4); return value; }
uint32_t oversized_count_bad(void) { uint32_t a[2],value; Descriptor d={a,sizeof(a)+1}; memset(d.pointer,0,d.allocation); memcpy(&value,d.pointer,4); return value; }
uint32_t count_changed_good(void) { Entry a[176]; Descriptor d={a,sizeof(a)}; uint32_t value; memset(d.pointer,0,d.allocation); d.allocation=0; memcpy(&value,&a[175].value,4); return value; }
uint32_t pointer_changed_good(void) { Value a,b; Descriptor d={&a,4}; uint32_t value; memset(d.pointer,0,d.allocation); d.pointer=&b; memcpy(&value,&a,4); return value; }
uint32_t reassign_before_bad(void) { Value a,b; void *p=&a; uint32_t value; p=&b; memset(p,0,4); memcpy(&value,&a,4); return value; }
uint32_t reassign_after_bad(void) { Value a,b; void *p=&a; uint32_t value; memset(p,0,4); p=&b; memcpy(&value,p,4); return value; }
uint32_t descriptor_reassign_bad(void) { Value a,b; Descriptor d={&a,4}; uint32_t value; memset(d.pointer,0,d.allocation); d.pointer=&b; memcpy(&value,d.pointer,4); return value; }
uint32_t wrong_stride_bad(void) { uint32_t a[2],value; uint64_t *p=(uint64_t*)a; memset(a,0,sizeof(a)); memcpy(&value,p+1,4); return value; }
uint32_t readonly_good(void) { Value a; void *p=&a; uint32_t value; memset(p,0,4); readonly_call(); memcpy(&value,p,4); return value; }
uint32_t model_alias_good(void) { Value a; void *p=identity(&a); uint32_t value; memset(p,0,4); memcpy(&value,&a,4); return value; }
uint32_t opaque_bad(void) { Value a; void *p=&a; uint32_t value; memset(p,0,4); opaque(); memcpy(&value,&a,4); return value; }
uint32_t alias_overwrite_bad(void) { Value a; void *p=&a; uint32_t source,value; memset(p,0,4); memcpy(p,&source,4); memcpy(&value,&a,4); return value; }
uint32_t descriptor_overwrite_bad(void) { Value a; Descriptor d={&a,4}; uint32_t source,value; memset(d.pointer,0,d.allocation); memcpy(d.pointer,&source,4); memcpy(&value,&a,4); return value; }
uint32_t indirect_bad(void (*fn)(void*)) { Value a; void *p=&a; uint32_t value; memset(p,0,4); fn(p); memcpy(&value,&a,4); return value; }
uint32_t released_bad(void) { Value a; void *p=&a; uint32_t value; memset(p,0,4); release(p); memcpy(&value,&a,4); return value; }
uint32_t escaped_slot_unknown(void) { Value a; void *p=&a; uint32_t value; overwrite(&p); memset(p,0,4); memcpy(&value,&a,4); return value; }
uint32_t escaped_descriptor_unknown(void) { Value a; Descriptor d={&a,4}; uint32_t value; overwrite(&d); memset(d.pointer,0,d.allocation); memcpy(&value,&a,4); return value; }
uint32_t partial_slot_unknown(void) { Value a; void *p=&a; uint32_t value; ((unsigned char*)&p)[1]=0; memset(p,0,4); memcpy(&value,&a,4); return value; }
uint32_t integer_cast_unknown(void) { Value a; void *p=(void*)(uintptr_t)(uint16_t)(uintptr_t)&a; uint32_t value; memset(p,0,4); memcpy(&value,&a,4); return value; }
uint32_t union_slot_unknown(void) { Value a; union { void *p; uintptr_t bits; } d; uint32_t value; d.p=&a; d.bits=0; memset(d.p,0,4); memcpy(&value,&a,4); return value; }
uint32_t ambiguous_unknown(int c) { Value a,b; void *p=c?(void*)&a:(void*)&b; uint32_t value; memset(p,0,4); memcpy(&value,&a,4); return value; }
uint32_t arithmetic_alias_unknown(void) { uint32_t a[2],value; uint32_t *p=a+1; memset(a,0,sizeof(a)); memcpy(&value,p,4); return value; }
uint32_t external_unknown(Entry *p) { uint32_t value; memset(p,0,176*sizeof(*p)); memcpy(&value,&p[175].value,4); return value; }
uint32_t allocation_unknown(void) { Entry *p=malloc(176*sizeof(*p)); uint32_t value=0; if(p) { memset(p,0,176*sizeof(*p)); memcpy(&value,&p[175].value,4); free(p); } return value; }
uint32_t disjoint_alias_unknown(void) { Value a,b; void *p=&a,*q=&b; uint32_t source=1,value; memset(p,0,4); memcpy(q,&source,4); memcpy(&value,&a,4); return value; }
uint32_t captured_length_good(void) { Value a; Descriptor d={&a,4}; uint32_t value; memset(d.pointer,0,d.allocation); memcpy(&value,d.pointer,d.allocation); d.allocation=0; return value; }
uint32_t captured_source_good(void) { Value a,b; Descriptor d={&a,4}; uint32_t value; memset(d.pointer,0,d.allocation); memcpy(&value,d.pointer,4); d.pointer=&b; return value; }
