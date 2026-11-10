/* Analysis only. Failing and unsupported cases must never be executed. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern int acquire(void **out, size_t capacity);
extern void release(void *p);
extern void opaque(void);
extern void readonly_call(void);
typedef struct { void *pointer; size_t capacity; } Descriptor;
uint32_t region_good(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_descriptor_good(void) { void *raw; Descriptor d; uint32_t v; if(acquire(&raw,8)<0)return 0; d.pointer=raw; d.capacity=8; memset(d.pointer,0,d.capacity); memcpy(&v,d.pointer,4); return v; }
uint32_t region_offset_good(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p+1,4); return v; }
uint32_t region_readonly_good(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); readonly_call(); memcpy(&v,p,4); return v; }
uint32_t region_partial_bad(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,1); memcpy(&v,p,4); return v; }
uint32_t region_failure_bad(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)>=0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_unguarded_bad(void) { void *raw; uint32_t *p,v; acquire(&raw,8); p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_uncleared_bad(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; memcpy(&v,p,4); return v; }
uint32_t region_released_bad(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); release(p); memcpy(&v,p,4); return v; }
uint32_t region_reclear_bad(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; release(p); memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_opaque_bad(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; opaque(); memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_reacquire_bad(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); release(p); if(acquire(&raw,8)<0)return 0; p=raw; memcpy(&v,p,4); return v; }
uint32_t region_old_alias_bad(void) { void *raw; uint32_t *p,*old,v; if(acquire(&raw,8)<0)return 0; old=raw; release(old); if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,old,4); return v; }
uint32_t region_oversized_bad(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,9); memcpy(&v,p,4); return v; }
uint32_t region_beyond_bad(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p+2,4); return v; }
uint32_t region_other_guard_bad(void) { void *raw,*other; uint32_t *p,v; int a=acquire(&raw,8),b=acquire(&other,8); if(b<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v+a; }
uint32_t region_changed_status_bad(void) { void *raw; uint32_t *p,v; int status=acquire(&raw,8); status=0; if(status<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_truncated_status_bad(void) { void *raw; uint32_t *p,v; unsigned char status=acquire(&raw,8); if(status!=0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_wrong_slot_bad(void) { uint32_t slot,*p,v; if(acquire((void**)&slot,8)<0)return 0; p=(void*)(uintptr_t)slot; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_missing_slot_bad(void) { void *raw; uint32_t *p,v; if(acquire(NULL,8)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_branch_bad(int c) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; if(c)release(p); memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_nested_unknown(void) { uint32_t v; { void *raw; uint32_t *p; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); } return v; }
uint32_t region_zero_bad(void) { void *raw; uint32_t *p,v; if(acquire(&raw,0)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_variable_unknown(size_t size) { void *raw; uint32_t *p,v; if(acquire(&raw,size)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_saved_good(void) { void *raw; uint32_t *p,v; int status=acquire(&raw,8); if(status<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_widened_good(void) { void *raw; uint32_t *p,v; long status=acquire(&raw,8); if(status<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_after_release_good(void) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; release(p); if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_before_release_good(void) { void *raw; uint32_t *p,v; int result; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); result=(v==0); release(p); return result; }
uint32_t region_two_clears_unknown(void) { void *raw; unsigned char *p; uint32_t v; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,2); memset(p+2,0,2); memcpy(&v,p,4); return v; }
uint32_t region_loop_unknown(void) { uint32_t v=0; for(int i=0;i<2;++i) { void *raw; uint32_t *p; if(acquire(&raw,8)<0)return 0; p=raw; memset(p,0,8); memcpy(&v,p,4); release(p); } return v; }
uint32_t region_indirect_bad(void (*fn)(void*)) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; fn(p); memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_slot_escape_bad(void (*fn)(void**)) { void *raw; uint32_t *p,v; if(acquire(&raw,8)<0)return 0; p=raw; fn((void**)&p); memset(p,0,8); memcpy(&v,p,4); return v; }
uint32_t region_descriptor_growth_bad(void) { void *raw; Descriptor d; uint32_t v; if(acquire(&raw,4)<0)return 0; d.pointer=raw; d.capacity=8; memset(d.pointer,0,d.capacity); memcpy(&v,d.pointer,4); return v; }
