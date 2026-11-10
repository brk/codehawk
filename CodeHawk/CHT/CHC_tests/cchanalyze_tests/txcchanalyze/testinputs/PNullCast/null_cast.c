/* Analysis-only controls for null pointer casts; unsafe functions never run. */
#include <stddef.h>
extern void needs_pointer(const char *p);
static char Global[2] = "x";
void null_direct_bad(void) { needs_pointer((const char *)0); }
void null_void_bad(void) { needs_pointer((const char *)(void *)0); }
void null_triple_bad(void) { needs_pointer((const char *)(char *)(void *)0); }
void null_macro_bad(void) { needs_pointer(NULL); }
int dereference_direct_bad(void) { return *(const int *)0; }
int dereference_void_bad(void) { return *(const int *)(void *)0; }
void local_good(void) { char Local[2]="x"; needs_pointer(Local); }
void global_good(void) { needs_pointer(Global); }
void literal_good(void) { needs_pointer("x"); }
void cast_local_good(void) { char Local[2]="x"; needs_pointer((const char *)(void *)Local); }
