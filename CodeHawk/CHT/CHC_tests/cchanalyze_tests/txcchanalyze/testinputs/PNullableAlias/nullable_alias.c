/* Analysis only: fgets may return NULL even with a valid initialized buffer. */
#include <stdio.h>
#include <string.h>
int fgets_unchecked_bad(FILE *stream)
{ char buffer[8]; char *p; memset(buffer,0,sizeof(buffer)); p=fgets(buffer,sizeof(buffer),stream); return *p; }
int fgets_guarded_good(FILE *stream)
{ char buffer[8]; char *p; memset(buffer,0,sizeof(buffer)); p=fgets(buffer,sizeof(buffer),stream); if(!p)return 0; return *p; }
int fgets_failed_bad(FILE *stream)
{ char buffer[8]; char *p; memset(buffer,0,sizeof(buffer)); p=fgets(buffer,sizeof(buffer),stream); if(p)return 0; return *p; }
int fgets_other_guard_bad(FILE *stream)
{ char buffer[8]; char *p,*other=buffer; memset(buffer,0,sizeof(buffer)); p=fgets(buffer,sizeof(buffer),stream); if(!other)return 0; return *p; }
int memcpy_alias_good(void)
{ char source[8]={0},dest[8]; char *p=memcpy(dest,source,sizeof(dest)); return *p; }
int memset_alias_good(void)
{ char dest[8]; char *p=memset(dest,0,sizeof(dest)); return *p; }
