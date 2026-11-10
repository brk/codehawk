/* Analysis only: the integer-address controls must never be executed. */
#include <stdint.h>
int absolute_direct(void) { return *(int *)(uintptr_t)1; }
int absolute_offset(void) { return *((int *)(uintptr_t)1 + 1); }
int absolute_member(void) {
    struct S { int x; int y; };
    return ((struct S *)(uintptr_t)1)->y;
}
int absolute_negative(void) { return *(int *)(intptr_t)-1; }
int absolute_zero(void) { return *(int *)(uintptr_t)0; }
int local_address(void) { int x=7; int *p=&x; return *p; }
static int global_value=7;
int global_address(void) { int *p=&global_value; return *p; }
int local_array(void) { int x[2]={7,8}; return x[1]; }
int literal_address(void) { const char *p="a"; return *p; }
