/* Guarded output controls are analyzed only; unsafe cases never execute. */
#include <stdint.h>
#include <stddef.h>
extern int acquire(void **out);
extern int acquire_zero(void **out);
extern int acquire_negative(void **out);
extern void opaque(void);
void *success_good(void) { void *p; int r=acquire(&p); if(r<0)return 0; return p; }
void *failure_bad(void) { void *p; int r=acquire(&p); if(r>=0)return 0; return p; }
void *unguarded_bad(void) { void *p; acquire(&p); return p; }
void *wrong_call_bad(void) { void *p,*q; int r=acquire(&p); int s=acquire(&q); if(s<0)return 0; (void)r; return p; }
void *overwritten_status_bad(void) { void *p; int r=acquire(&p); r=0; if(r<0)return 0; return p; }
void *saved_status_good(void) { void *p; int r=acquire(&p),s=r; r=-1; if(s<0)return 0; return p; }
void *field_good(void) { struct {void *p,*q;} d; int r=acquire(&d.p); if(r<0)return 0; return d.p; }
void *sibling_bad(void) { struct {void *p,*q;} d; int r=acquire(&d.p); if(r<0)return 0; return d.q; }
void *zero_good(void) { void *p; int r=acquire_zero(&p); if(r!=0)return 0; return p; }
void *zero_error_bad(void) { void *p; int r=acquire_zero(&p); if(r==0)return 0; return p; }
void *negative_good(void) { void *p; int r=acquire_negative(&p); if(r>=0)return 0; return p; }
void *narrow_status_unknown(void) { void *p; unsigned char r=(unsigned char)acquire(&p); if(r!=0)return 0; return p; }
extern int acquire_positive(void **out);
extern int acquire_nonpositive(void **out);
extern int acquire_nonzero(void **out);
extern int acquire_19(void **out);
extern int acquire_framed(void **out);
extern int status_only(void);
extern void readonly_call(void);
void *direct_if_good(void) { void *p; if(acquire(&p)<0)return 0; return p; }
void *positive_good(void) { void *p; int r=acquire_positive(&p); if(r<=0)return 0; return p; }
void *nonpositive_good(void) { void *p; int r=acquire_nonpositive(&p); if(r>0)return 0; return p; }
void *nonzero_good(void) { void *p; int r=acquire_nonzero(&p); if(r<=0)return 0; return p; }
void *constant_good(void) { void *p; int r=acquire_19(&p); if(r!=19)return 0; return p; }
void *wider_status_good(void) { void *p; long r=acquire(&p); if(r<0)return 0; return p; }
void *struct_status_good(void) { void *p; struct {int r;} s; s.r=acquire(&p); if(s.r<0)return 0; return p; }
void *readonly_good(void) { void *p; int r=acquire(&p); if(r<0)return 0; readonly_call(); return p; }
void *opaque_bad(void) { void *p; int r=acquire(&p); if(r<0)return 0; opaque(); return p; }
void *different_call_bad(void) { void *p,*q; int r=acquire_framed(&p),s=acquire_framed(&q); if(s<0)return 0; (void)r; return p; }
void *both_framed_good(void) { void *p,*q; int r=acquire_framed(&p),s=acquire_framed(&q); if(r<0||s<0)return 0; return p; }
void *status_only_bad(void) { void *p; int r=acquire(&p); r=status_only(); if(r<0)return 0; return p; }
void *normalized_error_bad(void) { void *p; int r=acquire(&p); if(r<0)r=0; if(r<0)return 0; return p; }
void *bool_status_bad(void) { void *p; _Bool r=acquire(&p); if(!r)return 0; return p; }
void *signed_narrow_bad(void) { void *p; int8_t r=(int8_t)acquire(&p); if(r<0)return 0; return p; }
void *unsigned_status_bad(void) { void *p; unsigned int r=(unsigned int)acquire(&p); if(r>100)return 0; return p; }
void *masked_status_bad(void) { void *p; int r=acquire(&p); r&=0; if(r<0)return 0; return p; }
void *arithmetic_status_bad(void) { void *p; int r=acquire(&p); if(r>0)return 0; r+=1; if(r<0)return 0; return p; }
void *partial_status_bad(void) { void *p; int r=acquire(&p); ((unsigned char*)&r)[0]=0; if(r<0)return 0; return p; }
void *union_status_bad(void) { void *p; union {int r;unsigned bits;} u; u.r=acquire(&p); u.bits=0; if(u.r<0)return 0; return p; }
void *volatile_status_unknown(void) { void *p; volatile int r=acquire(&p); if(r<0)return 0; return p; }
void *loop_status_unknown(void) { void *p; int previous=0; for(int i=0;i<2;++i) { int r=acquire(&p); if(previous<0)return 0; previous=r; } return p; }
void *branch_gap_bad(int c) { void *p; int r=0; if(c)r=acquire(&p); if(r<0)return 0; return p; }
uint32_t payload_bad(void) { void *p; int r=acquire(&p); if(r<0)return 0; return *(uint32_t*)p; }
typedef struct {void *p;void *q;} Descriptor;
extern int acquire_descriptor(Descriptor *out);
void *descriptor_good(void) { Descriptor d; int r=acquire_descriptor(&d); if(r<0)return 0; return d.p; }
void *descriptor_sibling_bad(void) { Descriptor d; int r=acquire_descriptor(&d); if(r<0)return 0; return d.q; }
extern void release(void *p);
void *nonzero_error_bad(void) { void *p; int r=acquire_nonzero(&p); if(r!=0)return 0; return p; }
void *released_bad(void) { void *p; int r=acquire(&p); if(r<0)return 0; release(p); return p; }
typedef union {uint32_t bits;uint16_t half;} Data;
extern int acquire_narrow(Data *out);
uint32_t narrow_field_bad(void) { Data d; int r=acquire_narrow(&d); if(r<0)return 0; return d.bits; }
void *checked_then_changed_good(void) { void *p; int r=acquire(&p); if(r<0)return 0; r=0; return p; }
extern double acquire_float(void **out);
void *float_guard_unknown(void) { void *p; double r=acquire_float(&p); if(r<0.0)return 0; return p; }
