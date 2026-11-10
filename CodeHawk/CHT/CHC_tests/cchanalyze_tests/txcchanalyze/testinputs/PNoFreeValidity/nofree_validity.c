/* Analysis only. No-free is a frame condition, not a memory origin. */
#include <stdint.h>
extern int *external_pointer(void);
extern int *valid_pointer(void);
extern void opaque_call(void);
void nofree_opaque(void) { int *p=external_pointer(); if(p)*p=7; }
void nofree_valid(void) { int *p=valid_pointer(); opaque_call();if(p)*p=7; }
void nofree_argument(int *p) { opaque_call();if(p)*p=7; }
void nofree_absolute(void) { *(int *)(uintptr_t)1=7; }
void nofree_local(void) { int x;int *p=&x;*p=7; }
