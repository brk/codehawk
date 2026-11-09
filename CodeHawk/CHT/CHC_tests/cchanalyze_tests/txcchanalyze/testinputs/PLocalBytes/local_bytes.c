/* Parser/analyzer controls only. Unsafe negative functions are never run. */
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
typedef union { uint32_t bits; float floating; uint16_t half; uint8_t bytes[4]; } Value;
typedef struct { uint8_t type, op; uint32_t mid, offset, mask; Value value; uint16_t count; } Entry;
extern void opaque(void);
extern void readonly_call(void);
extern void write_slot(uint32_t *slot);
extern void post_only(void *slot);
extern void release(void *p);
extern void user_clear(void *p, unsigned long n);
float full_array_good(void) { Entry a[176]; float value; memset(a,0,sizeof(a)); memcpy(&value,&a[175].value,4); return value; }
uint32_t full_scalar_good(void) { uint32_t a,value; memset(&a,0,sizeof(a)); memcpy(&value,&a,4); return value; }
uint32_t full_union_good(void) { Value a; uint32_t value; memset(&a,0,sizeof(a)); memcpy(&value,&a,4); return value; }
uint32_t field_good(void) { Entry a; uint32_t value; memset(&a.value,0,sizeof(a.value)); memcpy(&value,&a.value,4); return value; }
uint32_t nested_good(void) { struct { Entry a[176]; } s; uint32_t value; memset(&s,0,sizeof(s)); memcpy(&value,&s.a[175].value,4); return value; }
uint32_t partial_good(void) { unsigned char a[8]; uint32_t value; memset(a+1,0,5); memcpy(&value,a+1,4); return value; }
uint32_t partial_typed_good(void) { uint32_t a[2],value; memset((unsigned char*)a+1,0,5); memcpy(&value,(unsigned char*)a+1,4); return value; }
uint32_t partial_bad(void) { unsigned char a[8]; uint32_t value; memset(a+1,0,3); memcpy(&value,a+1,4); return value; }
uint32_t hole_bad(void) { unsigned char a[8]; uint32_t value; memset(a+1,0,5); memcpy(&value,a,4); return value; }
uint32_t sibling_bad(void) { Entry a; uint32_t value; memset(&a.mask,0,4); memcpy(&value,&a.value,4); return value; }
uint32_t narrow_union_bad(void) { Value a; uint32_t value; memset(&a.half,0,2); memcpy(&value,&a,4); return value; }
uint32_t conditional_bad(int c) { Value a; uint32_t value; if(c) memset(&a,0,4); memcpy(&value,&a,4); return value; }
uint32_t branches_good(int c) { unsigned char a[8]; uint32_t value; if(c) memset(a,0,8); else memset(a,1,4); memcpy(&value,a,4); return value; }
uint32_t branches_gap_bad(int c) { unsigned char a[8]; uint32_t value; if(c) memset(a,0,4); else memset(a+4,0,4); memcpy(&value,a,4); return value; }
uint32_t disjoint_write_good(void) { Value a; uint32_t b,value; memset(&a,0,4); b=1; memcpy(&value,&a,4); return value+(b-b); }
uint32_t disjoint_field_good(void) { Value a; Entry b; uint32_t value; memset(&a,0,4); b.mask=1; memcpy(&value,&a,4); return value; }
uint32_t readonly_good(void) { Value a; uint32_t value; memset(&a,0,4); readonly_call(); memcpy(&value,&a,4); return value; }
uint32_t framed_other_good(void) { Value a; uint32_t b,value; memset(&a,0,4); write_slot(&b); memcpy(&value,&a,4); return value; }
uint32_t overwrite_bad(void) { Value a; uint32_t source,value; memset(&a,0,4); memcpy(&a,&source,4); memcpy(&value,&a,4); return value; }
uint32_t field_overwrite_bad(void) { Entry a; uint32_t source,value; memset(&a,0,sizeof(a)); memcpy(&a.value,&source,4); memcpy(&value,&a.value,4); return value; }
uint32_t direct_alias_bad(void) { Value a; uint32_t value; memset(&a,0,4); *(uint32_t*)((unsigned char*)&a)=1; memcpy(&value,&a,4); return value; }
uint32_t opaque_bad(void) { Value a; uint32_t value; memset(&a,0,4); opaque(); memcpy(&value,&a,4); return value; }
uint32_t post_only_bad(void) { Value a; uint32_t value; memset(&a,0,4); post_only(&a); memcpy(&value,&a,4); return value; }
uint32_t indirect_bad(void (*fn)(void*)) { Value a; uint32_t value; memset(&a,0,4); fn(&a); memcpy(&value,&a,4); return value; }
uint32_t released_bad(void) { Value a; uint32_t value; memset(&a,0,4); release(&a); memcpy(&value,&a,4); return value; }
uint32_t beyond_bad(void) { Entry a[176]; uint32_t value; memset(a,0,sizeof(a)); memcpy(&value,&a[176].value,4); return value; }
uint32_t oversized_clear_bad(void) { Value a; uint32_t value; memset(&a,0,5); memcpy(&value,&a,4); return value; }
uint32_t volatile_unknown(void) { volatile Value a; uint32_t value; memset((void*)&a,0,4); memcpy(&value,(const void*)&a,4); return value; }
uint32_t user_clear_unknown(void) { Value a; uint32_t value; user_clear(&a,4); memcpy(&value,&a,4); return value; }
uint32_t clear_indirect_unknown(Entry *a) { uint32_t value; memset(a,0,176*sizeof(*a)); memcpy(&value,&a[175].value,4); return value; }
uint32_t allocation_unknown(void) { Entry *a=malloc(176*sizeof(*a)); uint32_t value=0; if(a) { memset(a,0,176*sizeof(*a)); memcpy(&value,&a[175].value,4); free(a); } return value; }
uint32_t loop_lifetime_unknown(void) { uint32_t value=0; for(int i=0;i<2;++i) { Value a; if(i==0) memset(&a,0,4); if(i==1) memcpy(&value,&a,4); } return value; }
uint32_t asm_unknown(void) { Value a; uint32_t value; memset(&a,0,4); __asm__ volatile("" : : "r"(&a) : "memory"); memcpy(&value,&a,4); return value; }
uint32_t two_clears_unknown(void) { unsigned char a[8]; uint32_t value; memset(a,0,2); memset(a+2,0,2); memcpy(&value,a,4); return value; }
uint32_t pointer_alias_unknown(void) { Entry a[176]; void *p=a; uint32_t value; memset(p,0,sizeof(a)); memcpy(&value,&a[175].value,4); return value; }
typedef struct { void *pointer; unsigned long allocation; } Descriptor;
uint32_t descriptor_unknown(void) { Entry a[176]; Descriptor d={a,sizeof(a)}; uint32_t value; memset(d.pointer,0,d.allocation); memcpy(&value,&a[175].value,4); return value; }
uint32_t vla_unknown(int n) { uint32_t value=0; if(n==4) { unsigned char a[n]; memset(a,0,n); memcpy(&value,a,4); } return value; }
