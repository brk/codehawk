/* Analyzed controls only; unsafe cases are never executed. */
#include <stddef.h>
#include <stdint.h>
#include <string.h>
extern int validate(const uint16_t *, int *, int *);
extern void event(int, ...);
extern void unknown(void);
extern int receive(const void **, size_t *);
extern int runloop(uint32_t *);
extern void perf(unsigned);
extern void readonly_call(void);
extern void post_only(int *);

int direct_good(const uint16_t *eq) {
    int index=0, depth=0;
    validate(eq, &index, &depth);
    return index+depth;
}
int loop_good(const uint16_t *eq, int n) {
    int index=0, depth=0, result=0;
    for(int i=0;i<n;i++) {
        validate(eq, &index, &depth);
        result += index+depth;
    }
    return result;
}
int loop_event_unknown(const uint16_t *eq, int n) {
    int index=0, depth=0, result=0;
    for(int i=0;i<n;i++) {
        validate(eq, &index, &depth);
        result += index+depth;
        event(index,depth);
    }
    return result;
}
int loop_reset_good(const uint16_t *eq, int n) {
    int result=0;
    for(int i=0;i<n;i++) {
        int index=0, depth=0;
        validate(eq, &index, &depth);
        result += index+depth;
        event(index,depth);
    }
    return result;
}
int loop_stale_unknown(const uint16_t *eq, int n, int active) {
    int index=0, depth=0, status=0, result=0;
    for(int i=0;i<n;i++) {
        if(active) status=validate(eq,&index,&depth);
        if(status==-1) result += index+depth;
        event(i);
    }
    return result;
}
const void *receive_good(void) {
    const void *ptr;
    size_t size;
    receive(&ptr,&size);
    return ptr;
}
const void *receive_perf_unknown(void) {
    const void *ptr;
    size_t size;
    receive(&ptr,&size);
    perf(1);
    return ptr;
}
uint32_t runloop_good(void) {
    uint32_t status=1;
    runloop(&status);
    return status;
}
uint32_t runloop_perf_unknown(void) {
    uint32_t status=1;
    runloop(&status);
    perf(1);
    return status;
}
static int *escaped;
int escaped_overwrite_bad(const uint16_t *eq) {
    int index=0,depth=0;
    escaped=&index;
    validate(eq,&index,&depth);
    unknown();
    return index;
}
int copy_then_unknown_bad(void) {
    int source=1, value;
    escaped=&value;
    memcpy(&value,&source,sizeof(value));
    unknown();
    return value;
}
int copy_then_indirect_bad(void (*fn)(void)) {
    int source=1, value;
    escaped=&value;
    memcpy(&value,&source,sizeof(value));
    fn();
    return value;
}
int copy_then_readonly_good(void) {
    int source=1, value;
    escaped=&value;
    memcpy(&value,&source,sizeof(value));
    readonly_call();
    return value;
}
int copy_then_postonly_bad(void) {
    int source=1, value, other;
    escaped=&value;
    memcpy(&value,&source,sizeof(value));
    post_only(&other);
    return value;
}
int stale_bound_bad(void) {
    int value=1, array[2]={0};
    escaped=&value;
    unknown();
    return array[value];
}
const void *receive_staged_good(void) {
    const void *out;
    size_t size;
    receive(&out,&size);
    const void *ptr=out;
    perf(1);
    return ptr;
}
uint32_t runloop_staged_good(void) {
    uint32_t out=1;
    runloop(&out);
    uint32_t status=out;
    perf(1);
    return status;
}
const void *receive_failure_good(void) {
    const void *ptr;
    size_t size;
    if(receive(&ptr,&size)<0) return ptr;
    return NULL;
}
uint32_t runloop_uninitialized_bad(void) {
    uint32_t status;
    runloop(&status);
    return status;
}
int indirect_return_bound_bad(int (*fn)(void)) {
    int index=1, array[2]={0};
    index=fn();
    return array[index];
}
