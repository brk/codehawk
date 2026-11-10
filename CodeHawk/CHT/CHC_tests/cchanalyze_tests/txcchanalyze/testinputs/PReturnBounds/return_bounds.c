/* Analysis only: invalid controls are never executed. */
#include <stdint.h>
#include <stdlib.h>
extern int *opaque_pointer(void);
extern int *bounded_pointer(void);
extern int *valid_pointer(void);
extern int *nullable_bounded_pointer(void);
extern int *error_bounded_pointer(void);
extern int *GlobalPointer;
int opaque_bounds(void) { int *p=opaque_pointer();return *p; }
int valid_only_bounds(void) { int *p=valid_pointer();return *p; }
int modeled_bounds(void) { int *p=bounded_pointer();return *p; }
int nullable_bounds(void) { int *p=nullable_bounded_pointer();if(p)return *p;return 0; }
int error_bounds(void) { int *p=error_bounded_pointer();if(p)return *p;return 0; }
int malloc_bounds(void) { int value=0;int *p=malloc(sizeof *p);if(p){*p=7;value=*p;free(p);}return value; }
int entry_bounds(int *p) { return *p; }
int global_pointer_bounds(void) { return *GlobalPointer; }
int local_bounds(void) { int x=7;int *p=&x;return *p; }
static int GlobalValue=7;
int global_object_bounds(void) { int *p=&GlobalValue;return *p; }
int local_array_bounds(void) { int x[2]={7,8};int *p=x;return *(p+1); }
int local_negative_bounds(void) { int x[2]={7,8};int *p=x;return *(p-1); }
int bad_caller_bounds(void) { return entry_bounds((int *)(uintptr_t)1); }
int good_caller_bounds(void) { int x=7;return entry_bounds(&x); }
