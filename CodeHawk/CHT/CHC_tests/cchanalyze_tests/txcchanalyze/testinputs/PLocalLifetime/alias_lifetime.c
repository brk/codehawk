/* Lifetime controls: unsafe functions are analyzed only, never executed. */
#include <stdint.h>
#include <string.h>
uint32_t function_scope_good(void) { uint32_t a,value; void *p=&a; memset(p,0,4); memcpy(&value,p,4); return value; }
uint32_t ended_block_bad(void) { void *p; { uint32_t a; p=&a; memset(p,0,4); } uint32_t value; memcpy(&value,p,4); return value; }
uint32_t ended_branch_bad(int c) { void *p; uint32_t value=0; if(c) { uint32_t a; p=&a; memset(p,0,4); } else return 0; memcpy(&value,p,4); return value; }
uint32_t live_nested_unknown(void) { uint32_t value; { uint32_t a; void *p=&a; memset(p,0,4); memcpy(&value,p,4); } return value; }
uint32_t top_branch_good(int c) { uint32_t a,value; void *p=&a; if(c) memset(p,0,4); else memset(p,1,4); memcpy(&value,p,4); return value; }
uint32_t ended_compound_bad(void) { void *p; { p=&(uint32_t){0}; memset(p,0,4); } uint32_t value; memcpy(&value,p,4); return value; }
uint32_t ended_statement_expr_bad(void) { void *p=({ uint32_t a; memset(&a,0,4); &a; }); uint32_t value; memcpy(&value,p,4); return value; }
uint32_t nested_slot_unknown(void) { uint32_t a,value; { void *p=&a; memset(p,0,4); memcpy(&value,p,4); } return value; }
uint32_t direct_nested_good(void) { uint32_t value; { uint32_t a; memset(&a,0,4); memcpy(&value,&a,4); } return value; }
uint32_t shadowed_bad(void) { uint32_t a; void *p; memset(&a,0,4); { uint32_t a; p=&a; } uint32_t value; memcpy(&value,p,4); return value; }
