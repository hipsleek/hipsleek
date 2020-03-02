/*
typedef struct __mavlink_message {
  xm_u16_t checksum; ///< sent at end of packet
  unsigned char magic; ///< protocol magic marker
  unsigned char len; ///< Length of payload
  unsigned char seq; ///< Sequence of packet
  unsigned char sysid; ///< ID of message sender system/aircraft
  unsigned char compid; ///< ID of the message sender component
  unsigned char msgid; ///< ID of message in payload
  unsigned int payload[MAVLINK_MAX_PAYLOAD_LEN+MAVLINK_NUM_CHECKSUM_BYTES];
} mavlink_message_t;
*/
struct checksum {
  int first;
  int second;
}

struct msg {
  int l;
  int payload[?];
  checksum cs;
}

int parse(int *buf, int len, msg *output)
  requires 
{
  if(buf[0] + 3 != len) {
    return 0;
  }

  output->l = buf[0];
  memcpy(output->payload, buf[1], output->l);
  output->checksum = buf[output->l+1];

  return 1;
}
