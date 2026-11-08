/* Mirrors LC's byte loop. Unsafe callers are analyzed, never executed. */
typedef unsigned char uint8;
typedef unsigned int uint32;
typedef union { uint32 Unsigned32; unsigned short Unsigned16; uint8 RawByte[4]; } LC_MultiType_t;

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

uint32 swap_full_good(void)
{
    uint8 source[4] = {1, 2, 3, 4};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.Unsigned32 = 0x00010203;
    LC_CopyBytesWithSwap(&dest, source, &map, 4);
    return dest.Unsigned32;
}

uint32 swap_partial_good(void)
{
    uint8 source[4] = {1, 2, 3, 4};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0xaabbccdd;
    map.Unsigned32 = 0x00000001;
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

uint32 swap_truncated_bad(void)
{
    uint8 source[2] = {1, 2};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.Unsigned32 = 0x00010203; /* map[0] selects byte 3 */
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

uint32 swap_uninitialized_source_bad(void)
{
    uint8 source[4];
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.Unsigned32 = 0x00010203;
    LC_CopyBytesWithSwap(&dest, source, &map, 4);
    return dest.Unsigned32;
}

uint32 swap_partial_source_bad(void)
{
    uint8 source[4];
    LC_MultiType_t dest, map;
    source[0] = 1;
    source[1] = 2;
    dest.Unsigned32 = 0;
    map.Unsigned32 = 0x00010203;
    LC_CopyBytesWithSwap(&dest, source, &map, 4);
    return dest.Unsigned32;
}

uint32 swap_uninitialized_map_bad(void)
{
    uint8 source[4] = {1, 2, 3, 4};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    LC_CopyBytesWithSwap(&dest, source, &map, 4);
    return dest.Unsigned32;
}

uint32 swap_uninitialized_tail_bad(void)
{
    uint8 source[4] = {1, 2, 3, 4};
    LC_MultiType_t dest, map;
    map.Unsigned32 = 0x00000001;
    LC_CopyBytesWithSwap(&dest, source, &map, 2);
    return dest.Unsigned32;
}

uint32 swap_oversized_bad(void)
{
    uint8 source[4] = {1, 2, 3, 4};
    LC_MultiType_t dest, map;
    dest.Unsigned32 = 0;
    map.Unsigned32 = 0x00010203;
    LC_CopyBytesWithSwap(&dest, source, &map, 5);
    return dest.Unsigned32;
}
