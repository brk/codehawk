/* Analysis-only getter transport controls. No unsafe case is executed. */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
struct Descriptor { void *pointer; size_t bytes; };
extern void *read_pointer(const struct Descriptor *);
extern void *unmodeled_pointer(const struct Descriptor *);
extern void opaque(void *);
extern void *root_identity(void *);
extern void *post_only_pointer(const struct Descriptor *);
extern void *readonly_unknown(const struct Descriptor *);

uint32_t direct_good(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; d.pointer=image; d.bytes=sizeof(image);
  memset(d.pointer,0,sizeof(image)); memcpy(&value,&image[1],sizeof(value)); return value; }
uint32_t getter_clear_good(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; void *p; d.pointer=image; d.bytes=sizeof(image);
  p=read_pointer(&d); memset(p,0,sizeof(image)); memcpy(&value,&image[1],sizeof(value)); return value; }
uint32_t getter_source_good(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; uint32_t *p; d.pointer=image; d.bytes=sizeof(image);
  memset(image,0,sizeof(image)); p=read_pointer(&d); memcpy(&value,p+1,sizeof(value)); return value; }
uint32_t short_clear_bad(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; void *p; d.pointer=image; d.bytes=sizeof(image);
  p=read_pointer(&d); memset(p,0,sizeof(image[0])); memcpy(&value,&image[1],sizeof(value)); return value; }
uint32_t uncleared_bad(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; uint32_t *p; d.pointer=image; d.bytes=sizeof(image);
  p=read_pointer(&d); memcpy(&value,p+1,sizeof(value)); return value; }
uint32_t missing_metadata_bad(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; void *p; d.bytes=sizeof(image);
  p=read_pointer(&d); memset(p,0,sizeof(image)); memcpy(&value,&image[1],sizeof(value)); return value; }
uint32_t changed_descriptor_good(void)
{ uint32_t image[2],other[2]; struct Descriptor d; uint32_t value; void *p; d.pointer=image; d.bytes=sizeof(image);
  p=read_pointer(&d); d.pointer=other; memset(p,0,sizeof(image)); memcpy(&value,&image[1],sizeof(value)); return value; }
uint32_t wrong_image_bad(void)
{ uint32_t image[2],other[2]; struct Descriptor d; uint32_t value; void *p; d.pointer=other; d.bytes=sizeof(other);
  p=read_pointer(&d); memset(p,0,sizeof(other)); memcpy(&value,&image[1],sizeof(value)); return value; }
uint32_t unmodeled_unknown(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; void *p; d.pointer=image; d.bytes=sizeof(image);
  p=unmodeled_pointer(&d); memset(p,0,sizeof(image)); memcpy(&value,&image[1],sizeof(value)); return value; }
uint32_t opaque_bad(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; void *p; d.pointer=image; d.bytes=sizeof(image);
  p=read_pointer(&d); memset(p,0,sizeof(image)); opaque(image); memcpy(&value,&image[1],sizeof(value)); return value; }
uint32_t released_bad(void)
{ uint32_t *image=malloc(8); struct Descriptor d; uint32_t value; void *p; if(!image)return 0;
  d.pointer=image; d.bytes=8; p=read_pointer(&d); memset(p,0,8); free(image); memcpy(&value,image+1,4); return value; }
uint32_t partial_metadata_bad(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; void *p; d.pointer=image; d.bytes=8;
  ((unsigned char *)&d.pointer)[0]=0; p=read_pointer(&d); memset(p,0,8); memcpy(&value,image+1,4); return value; }
uint32_t root_escape_bad(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; void *p,*q; d.pointer=image; d.bytes=8;
  q=root_identity(&d); memset(q,0,sizeof(d)); p=read_pointer(&d); memset(p,0,8); memcpy(&value,image+1,4); return value; }
uint32_t post_only_unknown(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; void *p; d.pointer=image; d.bytes=8;
  p=post_only_pointer(&d); memset(p,0,8); memcpy(&value,image+1,4); return value; }
uint32_t opaque_metadata_bad(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; void *p; d.pointer=image; d.bytes=8;
  opaque(&d); p=read_pointer(&d); memset(p,0,8); memcpy(&value,image+1,4); return value; }
uint32_t readonly_escape_unknown(void)
{ uint32_t image[2]; struct Descriptor d; uint32_t value; void *p,*q; d.pointer=image; d.bytes=8;
  q=readonly_unknown(&d); memset(q,0,1); p=read_pointer(&d); memset(p,0,8); memcpy(&value,image+1,4); return value; }
uint32_t union_metadata_unknown(void)
{ uint32_t image[2]; union {struct Descriptor d; unsigned char raw[sizeof(struct Descriptor)];} u;
  uint32_t value; void *p; u.d.pointer=image; u.d.bytes=8;
  p=read_pointer(&u.d); memset(p,0,8); memcpy(&value,image+1,4); return value; }
uint32_t nested_descriptor_unknown(void)
{ uint32_t image[2]; uint32_t value; void *p; { struct Descriptor d; d.pointer=image; d.bytes=8;
  p=read_pointer(&d); } memset(p,0,8); memcpy(&value,image+1,4); return value; }
uint32_t ended_image_bad(void)
{ struct Descriptor d; uint32_t value; uint32_t *p; { uint32_t image[2]; d.pointer=image; d.bytes=8; }
  p=read_pointer(&d); memset(p,0,8); memcpy(&value,p+1,4); return value; }
uint32_t freed_reclear_bad(void)
{ uint32_t *image=malloc(8); struct Descriptor d; uint32_t value; void *p; if(!image)return 0;
  d.pointer=image; d.bytes=8; p=read_pointer(&d); free(image); memset(p,0,8); memcpy(&value,image+1,4); return value; }
