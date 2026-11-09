/* Parser-only precision controls. Unsafe return reads never execute. */
extern int acquire(void **out);
extern void log_wide(long status);
extern void log_unsigned(unsigned status);
void *guard_no_log_good(void)
{
    void *p; int status = acquire(&p);
    if (status < 0) return 0;
    status = 0;
    return p;
}
void *guard_error_log_wide_good(void)
{
    void *p; int status = acquire(&p);
    if (status < 0) { log_wide((long)status); return 0; }
    status = 0;
    return p;
}
void *guard_error_log_narrow_good(void)
{
    void *p; int status = acquire(&p);
    if (status < 0) { log_unsigned((unsigned)status); return 0; }
    status = 0;
    return p;
}
void *guard_cast_prefix_unknown(void)
{
    void *p; int status = acquire(&p);
    unsigned converted = (unsigned)status;
    (void)converted;
    if (status < 0) return 0;
    return p;
}
void *guard_cast_rejoin_unknown(int condition)
{
    void *p; int status = acquire(&p);
    unsigned converted = 0;
    if (condition) converted = (unsigned)status;
    (void)converted;
    if (status < 0) return 0;
    return p;
}
void *guard_normalized_error_bad(void)
{
    void *p; int status = acquire(&p);
    if (status < 0) { log_unsigned((unsigned)status); status = 0; }
    if (status < 0) return 0;
    return p;
}
