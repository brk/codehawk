/* Analysis only. Deliberately unsafe cases must never be executed.
 * Header length, capacity, initialized bytes and lifetime are independent. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

extern void unknown_producer(unsigned char *);
extern const unsigned char *receive_packet(void);
extern void next_receive(void);

uint32_t received_local_good(void)
{
    unsigned char packet[12] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11};
    uint32_t datum;
    memcpy(&datum, packet + 8, sizeof(datum));
    return datum;
}

uint32_t header_only_truncated_bad(void)
{
    unsigned char packet[12] = {0};
    const uint32_t header_length = 100, offset = 64;
    uint32_t datum = 0;
    if (offset <= header_length && sizeof(datum) <= header_length - offset)
        memcpy(&datum, packet + offset, sizeof(datum));
    return datum;
}

uint32_t capacity_without_initialization_bad(void)
{
    unsigned char packet[12];
    uint32_t datum;
    packet[0] = 0;
    packet[1] = 0;
    memcpy(&datum, packet + 8, sizeof(datum));
    return datum;
}

uint32_t missing_last_byte_bad(void)
{
    unsigned char packet[4];
    uint32_t datum;
    packet[0] = 1;
    packet[1] = 2;
    packet[2] = 3;
    memcpy(&datum, packet, sizeof(datum));
    return datum;
}

uint32_t zero_before_overwrite_bad(void)
{
    unsigned char packet[4] = {0}, source[4];
    uint32_t datum;
    memcpy(packet, source, sizeof(packet));
    memcpy(&datum, packet, sizeof(datum));
    return datum;
}

uint32_t unknown_producer_bad(void)
{
    unsigned char packet[4] = {0};
    uint32_t datum;
    unknown_producer(packet);
    memcpy(&datum, packet, sizeof(datum));
    return datum;
}

uint32_t receive_without_contract_bad(void)
{
    const unsigned char *packet = receive_packet();
    uint32_t datum = 0;
    if (packet != NULL)
        memcpy(&datum, packet + 8, sizeof(datum));
    return datum;
}

uint32_t next_receive_without_frame_bad(void)
{
    const unsigned char *packet = receive_packet();
    uint32_t datum = 0;
    if (packet != NULL)
    {
        next_receive();
        memcpy(&datum, packet + 8, sizeof(datum));
    }
    return datum;
}

uint32_t explicitly_released_bad(void)
{
    unsigned char *packet = malloc(4);
    uint32_t datum = 0;
    if (packet != NULL)
    {
        memset(packet, 0, 4);
        free(packet);
        memcpy(&datum, packet, sizeof(datum));
    }
    return datum;
}

uint32_t received_typed_stride_good(void)
{
    uint16_t packet[6] = {1, 2, 3, 4, 5, 6};
    uint32_t datum;
    memcpy(&datum, packet + 4, sizeof(datum));
    return datum;
}

uint32_t received_nested_offset_good(void)
{
    uint16_t packet[2][3] = {{1, 2, 3}, {4, 5, 6}};
    uint32_t datum;
    memcpy(&datum, ((unsigned char *)packet) + 8, sizeof(datum));
    return datum;
}

uint32_t received_composed_offset_good(void)
{
    unsigned char packet[12] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11};
    uint32_t datum;
    memcpy(&datum, (packet + 4) + 4, sizeof(datum));
    return datum;
}

uint32_t offset_missing_last_byte_bad(void)
{
    unsigned char packet[12];
    uint32_t datum;
    packet[8] = 1;
    packet[9] = 2;
    packet[10] = 3;
    memcpy(&datum, packet + 8, sizeof(datum));
    return datum;
}

uint32_t typed_stride_truncated_bad(void)
{
    uint16_t packet[6] = {1, 2, 3, 4, 5, 6};
    uint32_t datum;
    memcpy(&datum, packet + 5, sizeof(datum));
    return datum;
}

uint32_t negative_offset_bad(void)
{
    unsigned char packet[4] = {1, 2, 3, 4};
    uint32_t datum;
    memcpy(&datum, packet - 1, sizeof(datum));
    return datum;
}

uint32_t one_past_source_bad(void)
{
    unsigned char packet[4] = {1, 2, 3, 4};
    uint32_t datum;
    memcpy(&datum, packet + 4, sizeof(datum));
    return datum;
}
