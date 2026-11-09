/* Allocation controls are analyzed only, never executed. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void opaque(void);
extern void readonly_call(void);
uint32_t heap_full_good(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_partial_bad(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,1); memcpy(&value,p,4); return value; }
uint32_t heap_failed_bad(void) { uint32_t *p=malloc(8),value; if(p) return 0; memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_free_bad(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,8); free(p); memcpy(&value,p,4); return value; }
uint32_t heap_uncleared_bad(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memcpy(&value,p,4); return value; }
uint32_t heap_reassign_bad(void) { uint32_t *p=malloc(8),*q=malloc(8),value; if(!p || !q) return 0; memset(p,0,8); p=q; memcpy(&value,p,4); return value; }
typedef union { uint32_t bits; float fp; } Value;
typedef struct { uint8_t type,op; uint32_t mid,offset,mask; Value value; uint16_t count; } Entry;
typedef struct { void *pointer; size_t capacity; } Descriptor;
extern void *external_alloc(size_t size);
uint32_t heap_typed_offset_good(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,8); memcpy(&value,p+1,4); return value; }
uint32_t heap_byte_offset_good(void) { unsigned char *p=malloc(8); uint32_t value; if(!p) return 0; memset(p+1,0,5); memcpy(&value,p+1,4); return value; }
uint32_t heap_descriptor_good(void) { Descriptor d; uint32_t value; d.pointer=malloc(8); d.capacity=8; if(!d.pointer) return 0; memset(d.pointer,0,d.capacity); memcpy(&value,d.pointer,4); return value; }
uint32_t heap_entry_good(void) { Entry *p=malloc(176*sizeof(*p)); uint32_t value; if(!p) return 0; memset(p,0,176*sizeof(*p)); memcpy(&value,&p[175].value,4); return value; }
uint32_t heap_before_free_good(void) { uint32_t *p=malloc(8),value; int result; if(!p) return 0; memset(p,0,8); memcpy(&value,p,4); result=(value==0); free(p); return result; }
uint32_t heap_captured_good(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,8); memcpy(&value,p,4); p=0; return value; }
uint32_t heap_size_captured_unknown(void) { size_t size=8; uint32_t *p=malloc(size),value; if(!p) return 0; size=1; memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_readonly_good(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,8); readonly_call(); memcpy(&value,p,4); return value; }
uint32_t heap_opaque_bad(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,8); opaque(); memcpy(&value,p,4); return value; }
uint32_t heap_overwrite_bad(void) { uint32_t *p=malloc(8),source,value; if(!p) return 0; memset(p,0,8); memcpy(p,&source,4); memcpy(&value,p,4); return value; }
uint32_t heap_other_clear_unknown(void) { uint32_t *p=malloc(8),*q=malloc(8),value; if(!p || !q) return 0; memset(p,0,8); memset(q,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_nonnull_other_bad(void) { uint32_t *p=malloc(8),*q=malloc(8),value; if(!q || p) return 0; memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_short_alloc_bad(void) { unsigned char *p=malloc(1); uint32_t value; if(!p) return 0; memset(p,0,1); memcpy(&value,p,4); return value; }
uint32_t heap_oversized_clear_bad(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,9); memcpy(&value,p,4); return value; }
uint32_t heap_beyond_bad(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,8); memcpy(&value,p+2,4); return value; }
uint32_t heap_wrong_stride_bad(void) { uint64_t *p=malloc(8); uint32_t value; if(!p) return 0; memset(p,0,8); memcpy(&value,p+1,4); return value; }
uint32_t heap_partial_field_unknown(void) { Entry *p=malloc(176*sizeof(*p)); uint32_t value; if(!p) return 0; memset(p,0,176*sizeof(*p)-8); memcpy(&value,&p[175].value,4); return value; }
uint32_t heap_arithmetic_slot_unknown(void) { uint32_t *p=malloc(8),*q,value; if(!p) return 0; q=p+1; memset(p,0,8); memcpy(&value,q,4); return value; }
uint32_t heap_realloc_unknown(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,8); p=realloc(p,8); if(!p) return 0; memcpy(&value,p,4); return value; }
uint32_t heap_reuse_bad(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,8); free(p); p=malloc(8); if(!p) return 0; memcpy(&value,p,4); return value; }
uint32_t heap_external_allocator_unknown(void) { uint32_t *p=external_alloc(8),value; if(!p) return 0; memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_no_guard_unknown(void) { uint32_t *p=malloc(8),value; memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_nested_slot_unknown(void) { uint32_t value; { uint32_t *p=malloc(8); if(!p) return 0; memset(p,0,8); memcpy(&value,p,4); } return value; }
uint32_t heap_integer_cast_unknown(void) { uint32_t *p=(uint32_t*)(uintptr_t)(uint16_t)(uintptr_t)malloc(8),value; if(!p) return 0; memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_zero_unknown(void) { uint32_t *p=malloc(0),value; if(!p) return 0; memset(p,0,0); memcpy(&value,p,4); return value; }
uint32_t heap_external_unknown(uint32_t *p) { uint32_t value; if(!p) return 0; memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_two_clears_unknown(void) { unsigned char *p=malloc(8); uint32_t value; if(!p) return 0; memset(p,0,2); memset(p+2,0,2); memcpy(&value,p,4); return value; }
uint32_t heap_reclear_after_free_bad(void) { uint32_t *p=malloc(8),value; if(!p) return 0; memset(p,0,8); free(p); memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_opaque_reclear_unknown(void) { uint32_t *p=malloc(8),value; if(!p) return 0; opaque(); memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_entry_beyond_bad(void) { Entry *p=malloc(176*sizeof(*p)); uint32_t value; if(!p) return 0; memset(p,0,176*sizeof(*p)); memcpy(&value,&p[176].value,4); return value; }
uint32_t heap_indirect_reclear_unknown(void (*fn)(void*)) { uint32_t *p=malloc(8),value; if(!p) return 0; fn(p); memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_escaped_slot_unknown(void (*fn)(void**)) { uint32_t *p=malloc(8),value; if(!p) return 0; fn((void**)&p); memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_branch_live_bad(int c) { uint32_t *p=malloc(8),value; if(!p) return 0; if(c) free(p); memset(p,0,8); memcpy(&value,p,4); return value; }
uint32_t heap_loop_unknown(void) { uint32_t value=0; for(int i=0;i<2;++i) { uint32_t *p=malloc(8); if(!p) return 0; memset(p,0,8); memcpy(&value,p,4); free(p); } return value; }
uint32_t heap_field_wide_bad(void) { Entry *p=malloc(176*sizeof(*p)); uint64_t value; if(!p) return 0; memset(p,0,176*sizeof(*p)); memcpy(&value,&p[175].value,8); return (uint32_t)value; }
