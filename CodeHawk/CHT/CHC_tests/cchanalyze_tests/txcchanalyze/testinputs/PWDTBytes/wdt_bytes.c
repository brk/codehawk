/* Reduced byte/region controls. Unsafe cases are analyzed, never executed. */
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

typedef union { uint32_t bits; float floating; uint8_t bytes[4]; } Value;
typedef struct { uint8_t type, op; uint32_t mid, offset, mask; Value value; uint16_t count; } Entry;
extern void require_bytes(uint32_t *p);
extern void require_raw_bytes(uint32_t *p);
extern void require_indices(uint32_t *p);
extern void opaque(void);
extern void readonly_call(void);
extern int acquire(void **out);
extern void release(void *p);
extern void fill(void *p);

void bytes_good(void) { uint32_t a[2]={1,2}; require_bytes(a); }
void bytes_short_bad(void) { uint32_t a=1; require_bytes(&a); }
void raw_bytes_good(void) { uint32_t a[2]={1,2}; require_raw_bytes(a); }
void raw_bytes_short_bad(void) { uint32_t a=1; require_raw_bytes(&a); }
void indices_good(void) { uint32_t a[2]={1,2}; require_indices(a); }
void indices_short_bad(void) { uint32_t a=1; require_indices(&a); }
float scalar_good(void) { uint32_t bits=0; float value; memcpy(&value,&bits,4); return value; }
float union_good(void) { Value v; float value; v.bits=0; memcpy(&value,&v,4); return value; }
float field_good(void) { Entry e; float value; e.value.bits=0; memcpy(&value,&e.value,4); return value; }
float last_good(void) { Entry e[176]; float value; e[175].value.bits=0; memcpy(&value,&e[175].value,4); return value; }
float partial_bad(void) { Value v; float value; v.bytes[0]=0; memcpy(&value,&v,4); return value; }
float sibling_bad(void) { Entry e; float value; e.mask=0; memcpy(&value,&e.value,4); return value; }
float readonly_good(void) { Value v; float value; v.bits=0; readonly_call(); memcpy(&value,&v,4); return value; }
float overwritten_bad(void) { Value v; float value; v.bits=0; fill(&v); memcpy(&value,&v,4); return value; }
float opaque_bad(void) { Value v; float value; v.bits=0; opaque(); memcpy(&value,&v,4); return value; }
float entry_unknown(Entry *image) { float value; memcpy(&value,&image[175].value,4); return value; }
float loop_unknown(Entry *image) { float value=0; for(int i=0;i<176;++i) memcpy(&value,&image[i].value,4); return value; }
float cleared_unknown(void) { Entry e[176]; float value; memset(e,0,sizeof(e)); memcpy(&value,&e[175].value,4); return value; }
float allocated_unknown(void) { Entry *e=malloc(176*sizeof(*e)); float value=0; if(e) { memset(e,0,176*sizeof(*e)); memcpy(&value,&e[175].value,4); free(e); } return value; }
float acquired_unknown(void) { void *p; float value=0; if(acquire(&p)==0) memcpy(&value,&((Entry*)p)[175].value,4); return value; }
float failed_acquire_bad(void) { void *p; float value; acquire(&p); memcpy(&value,p,4); return value; }
float released_bad(void) { void *p; float value=0; if(acquire(&p)==0) { release(p); memcpy(&value,p,4); } return value; }
