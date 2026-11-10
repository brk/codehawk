/* Analysis only: bad controls must never be executed. */
#include <stdint.h>
#include <stdlib.h>
extern int *external_pointer(void);
extern int *valid_pointer(void);
extern int *new_pointer(void);
extern int *nullable_valid_pointer(void);
extern int *error_pointer(void);
extern int *new_only_pointer(void);
extern int *heap_only_pointer(void);
extern void opaque_call(void);
extern void readonly_call(void);
void opaque_use(void) { int *p=external_pointer(); if(p)*p=7; }
void opaque_readonly(void) { int *p=external_pointer(); readonly_call(); if(p)*p=7; }
static int *integer_pointer(void) { return (int *)(uintptr_t)1; }
void integer_return_use(void) { int *p=integer_pointer(); if(p)*p=7; }
void valid_use(void) { int *p=valid_pointer(); if(p)*p=7; }
void valid_readonly(void) { int *p=valid_pointer(); readonly_call(); if(p)*p=7; }
void valid_opaque(void) { int *p=valid_pointer(); opaque_call(); if(p)*p=7; }
void new_use(void) { int *p=new_pointer(); if(p)*p=7; }
void nullable_use(void) { int *p=nullable_valid_pointer(); if(p)*p=7; }
void error_use(void) { int *p=error_pointer(); if(p)*p=7; }
void new_only_use(void) { int *p=new_only_pointer(); if(p)*p=7; }
void heap_only_use(void) { int *p=heap_only_pointer(); if(p)*p=7; }
void malloc_use(void) { int *p=malloc(sizeof *p); if(p){*p=7;free(p);} }
void malloc_freed(void) { int *p=malloc(sizeof *p); if(p){free(p);*p=7;} }
void local_use(void) { int x;int *p=&x;*p=7; }
static int global_value;
void global_use(void) { int *p=&global_value;*p=7; }
void argument_use(int *p) { if(p)*p=7; }
void argument_readonly(int *p) { readonly_call();if(p)*p=7; }
void argument_opaque(int *p) { opaque_call();if(p)*p=7; }
void argument_freed(int *p) { free(p);if(p)*p=7; }
void argument_good_caller(void) { int x;argument_use(&x); }
void argument_bad_caller(void) { argument_use((int *)(uintptr_t)1); }
