/* Analysis-only printf precision controls; unsafe cases are never executed. */
#include <stdio.h>
void bounded_constant_good(void)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%.4s",src); }
void bounded_argument_good(void)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%.*s",4,src); }
void terminated_good(void)
{ char src[5]="abcd",dst[16]; snprintf(dst,sizeof(dst),"%s",src); }
void literal_good(void)
{ char dst[16]; snprintf(dst,sizeof(dst),"%s","abcd"); }
void negative_precision_bad(void)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%.*s",-1,src); }
void excessive_precision_bad(void)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%.5s",src); }
void unbounded_bad(void)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%s",src); }
void bounded_sizeof_good(void)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%.*s",(int)sizeof(src),src); }
void bounded_width_precision_good(void)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%*.*s",10,4,src); }
void bounded_multiple_good(void)
{ char src[4]={'a','b','c','d'},other[2]={'e','f'},dst[16]; snprintf(dst,sizeof(dst),"%.*s:%.*s",4,src,2,other); }
void fieldwidth_bad(void)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%4s",src); }
void unknown_precision_unknown(int precision)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%.*s",precision,src); }
void uninitialized_prefix_bad(void)
{ char src[4],dst[16]; snprintf(dst,sizeof(dst),"%.4s",src); }
void partial_prefix_bad(void)
{ char src[4],dst[16]; src[0]='a'; snprintf(dst,sizeof(dst),"%.4s",src); }
void bounded_offset_good(void)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%.2s",src+2); }
void excessive_offset_bad(void)
{ char src[4]={'a','b','c','d'},dst[16]; snprintf(dst,sizeof(dst),"%.4s",src+2); }
void zero_precision_good(void)
{ char src[1],dst[16]; snprintf(dst,sizeof(dst),"%.0s",src); }
void zero_null_bad(void)
{ char dst[16]; snprintf(dst,sizeof(dst),"%.0s",(char*)0); }
#include <wchar.h>
void wide_precision_unknown(void)
{ wchar_t src[4]={'a','b','c','d'}; char dst[16]; snprintf(dst,sizeof(dst),"%.*ls",4,src); }
