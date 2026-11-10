/* Analysis only: ended-scope controls must never be executed. */
int live_local_read(void) { int x=7; int *p=&x; return *p; }
void live_local_write(void) { int x; int *p=&x; *p=7; }
int ended_local_read(void) { int *p; { int x=7; p=&x; } return *p; }
void ended_local_write(void) { int *p; { int x; p=&x; } *p=7; }
void ended_branch_write(int c) { int *p; if(c) { int x; p=&x; } else return; *p=7; }
void ended_compound_write(void) { int *p; { p=&(int){0}; } *p=7; }
void ended_expression_write(void) { int *p=({ int x; &x; }); *p=7; }
void shadowed_local_write(void) { int x; int *p=&x; { int x; p=&x; } *p=7; }
void live_nested_write(void) { { int x; int *p=&x; *p=7; } }
void live_branch_write(int c) { int x; int *p=&x; if(c) *p=7; else *p=8; }
void live_nested_static_write(void) { int *p; { static int x; p=&x; } *p=7; }
int scope_global;
void live_global_write(void) { int *p=&scope_global; *p=7; }
void live_offset_write(void) { int a[2]; int *p=a+1; *p=7; }
struct scope_pair { int a,b; };
void ended_field_write(void) { int *p; { struct scope_pair x; p=&x.b; } *p=7; }
