/* Initialized-entry requirements must be visible before each call. */
typedef struct { int value, sibling; } Pair;
extern void optional(int *out);
extern void field(Pair *out);
int entry_good(void) { int value=0; optional(&value); return value; }
int entry_bad(void) { int value; optional(&value); return value; }
int field_good(void) { Pair p; p.value=0; field(&p); return p.value; }
int field_bad(void) { Pair p; field(&p); return p.value; }
int sibling_bad(void) { Pair p; p.sibling=0; field(&p); return p.value; }
