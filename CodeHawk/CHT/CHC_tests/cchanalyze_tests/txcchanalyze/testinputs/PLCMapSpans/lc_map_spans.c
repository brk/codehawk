/* Production LC loop with explicit map/span contracts. Unsafe callers are not run. */
typedef unsigned char uint8;
typedef unsigned int uint32;
typedef union LC_MultiType { uint32 Unsigned32; unsigned short Unsigned16; uint8 RawByte[4]; } LC_MultiType_t;

void LC_CopyBytesWithSwap(LC_MultiType_t *DestBuffer, const uint8 *SrcPtr, LC_MultiType_t *SwapMap, uint32 NumBytes)
{
    uint8 *DestPtr;
    const uint8 *SwapMapPtr;
    DestPtr = (uint8 *)DestBuffer;
    SwapMapPtr = (const uint8 *)SwapMap;
    while (NumBytes > 0)
    {
        --NumBytes;
        DestPtr[NumBytes] = SrcPtr[SwapMapPtr[NumBytes] & 0x3];
    }
}

uint32 map_two_bytes_good(void)
{
    const uint8 source[2] = {0x12, 0x34};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0xaabbccdd;
    map.RawByte[0] = 1; map.RawByte[1] = 0;
    map.RawByte[2] = 0; map.RawByte[3] = 0;
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

uint32 map_four_bytes_good(void)
{
    const uint8 source[4] = {0x12, 0x34, 0x56, 0x78};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.RawByte[0] = 3; map.RawByte[1] = 2;
    map.RawByte[2] = 1; map.RawByte[3] = 0;
    LC_CopyBytesWithSwap(&dest, source, &map, 4);
    return dest.Unsigned32;
}

uint32 map_first_index_bad(void)
{
    const uint8 source[2] = {0x12, 0x34};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.RawByte[0] = 3; map.RawByte[1] = 0;
    map.RawByte[2] = 0; map.RawByte[3] = 0;
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

uint32 map_second_index_bad(void)
{
    const uint8 source[2] = {0x12, 0x34};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.RawByte[0] = 0; map.RawByte[1] = 3;
    map.RawByte[2] = 0; map.RawByte[3] = 0;
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

uint32 map_truncated_source_bad(void)
{
    const uint8 source[1] = {0x12};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.RawByte[0] = 1; map.RawByte[1] = 0;
    map.RawByte[2] = 0; map.RawByte[3] = 0;
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

uint32 map_uninitialized_source_bad(void)
{
    uint8 source[2];
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.RawByte[0] = 1; map.RawByte[1] = 0;
    map.RawByte[2] = 0; map.RawByte[3] = 0;
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

uint32 map_missing_tail_bad(void)
{
    const uint8 source[2] = {0x12, 0x34};
    LC_MultiType_t dest, map;
    map.RawByte[0] = 1; map.RawByte[1] = 0;
    map.RawByte[2] = 0; map.RawByte[3] = 0;
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

extern void unknown_map_writer(LC_MultiType_t *);
uint32 map_changed_bad(void)
{
    const uint8 source[2] = {0x12, 0x34};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.RawByte[0] = 1; map.RawByte[1] = 0;
    map.RawByte[2] = 0; map.RawByte[3] = 0;
    unknown_map_writer(&map);
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

uint32 map_wrapped_byte_bad(void)
{
    const uint8 source[2] = {0x12, 0x34};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.RawByte[0] = (uint8)-1; map.RawByte[1] = 0;
    map.RawByte[2] = 0; map.RawByte[3] = 0;
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

void observe_map(void) {}
uint32 map_framed_good(void)
{
    const uint8 source[2] = {0x12, 0x34};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.RawByte[0] = 1; map.RawByte[1] = 0;
    map.RawByte[2] = 0; map.RawByte[3] = 0;
    observe_map();
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}
