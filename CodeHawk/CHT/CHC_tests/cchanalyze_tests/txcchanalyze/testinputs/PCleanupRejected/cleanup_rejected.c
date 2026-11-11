union sample { unsigned char byte; unsigned int word; };
unsigned Kind;
extern unsigned int consume(union sample *value);

static void change_kind(unsigned *unused)
{
    (void)unused;
    Kind = 3;
}

unsigned int cleanup_selector(unsigned int input)
{
    union sample value;
    switch (Kind) {
        case 1: value.byte = input & 255; break;
        default: value.word = input; break;
    }
    { unsigned guard __attribute__((cleanup(change_kind))); }
    switch (Kind) {
        case 3: return consume(&value);
        default: return 0;
    }
}
