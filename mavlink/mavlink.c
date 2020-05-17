#define MAVLINK_MAX_PAYLOAD_LEN 255 ///< Maximum payload length
#define MAVLINK_NUM_CHECKSUM_BYTES 2

typedef unsigned short xm_u16_t;

typedef struct _checksum {
  int first;
  int second;
} checksum;

typedef struct __mavlink_message {
  //xm_u16_t checksum; ///< sent at end of packet
  checksum checksum;
  unsigned char magic; ///< protocol magic marker
  unsigned char len; ///< Length of payload
  unsigned char seq; ///< Sequence of packet
  unsigned char sysid; ///< ID of message sender system/aircraft
  unsigned char compid; ///< ID of the message sender component
  unsigned char msgid; ///< ID of message in payload
  // unsigned int payload[MAVLINK_MAX_PAYLOAD_LEN+MAVLINK_NUM_CHECKSUM_BYTES];
  int *payload;
} mavlink_message_t;

/*@
pred arr_buf<root,end,max_size,size,v> == self::int_star<v> * q::arr_buf<root,end,max_size,size-1,_> & q=self+1
  or self::int_star<v> & self=end & size = 1
  inv root <= self <= end
  & end - root + 1 = max_size
  &  1 <= size <= max_size;

pred buffer_helper<length,n,ma,n,se,sy,co,ms,f1,s1> ==
  self::int_star<ma>
  * buf1::int_star<n>
  * buf2::int_star<se>
  * buf3::int_star<sy>
  * buf4::int_star<co>
  * buf5::int_star<ms>
  * buf6::arr_buf<self, end, length, n, _>
  * end1::int_star<f1>
  * end::int_star<s1>
  & end1 = end - 1
  & buf1 = self + 1
  & buf2 = self + 2
  & buf3 = self + 3
  & buf4 = self + 4
  & buf5 = self + 5
  & buf6 = self + 6
  & length = n + 8;
*/

void *memcpy(int *dest, int *src, int length) __attribute__((noreturn))
/*@
  requires dest=null & src = null
  ensures  true;
  requires src::arr_buf<_,_,_,_,_> & dest=null
  ensures  true;
  requires dest::arr_buf<_,_,_,_,_> & src=null
  ensures  true;
  requires dest::arr_buf<r2,e2,m2,s2,v2> * src::arr_buf<r1,e1,m1,s1,v1>  & length>=0 & s1>=length & s2>=length
  ensures  dest::arr_buf<r2,e2,m2,s2,v1> * src::arr_buf<r1,e1,m1,s1,v1>;
  //ensures true;
*/;

int* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::arr_buf<r,e,m,s,v> & s=size;
  }
*/;

void* cast_int(int* x)  __attribute__ ((noreturn))
/*@
case {
  x != null -> requires  x::memLoc<h2,s2>
                    ensures  res::void*<_> * res::memLoc<h2,s2> & h2;
  x = null -> requires true ensures res = null;
}
 */;

// int parse_mavlink_msg(char ma,
//                       char l,
//                       char se,
//                       char sy,
//                       char co,
//                       char ms,
//                       char ch,
//                       int *p, int len, mavlink_message_t *msg)
// /*@
//   requires msg::__mavlink_message<_,_,_,_,_,_,_,payl>@M
//             * p::memLoc<_,l>
//   ensures true;
// */
// {
//     if (l + 8 != len)
//         return 0;
//     msg->magic = ma;
//     msg->len = l;
//     msg->seq = se;
//     msg->sysid = sy;
//     msg->compid = co;
//     msg->msgid = ms;
//     msg->checksum = ch;
//     // int pa0 = msg->payload[0];
//     // int *payload_buf = &pa0; // do we put payload into precond as a memLoc?
//     // dprint;
//     msg->payload = malloc(msg->len);
//     void *pb = cast_int(msg->payload);
//     void *pv = cast_int(p);
//     memcpy(pb, pv, msg->len);
//     return 1;
// }

int parse_mavlink_msg_buggy(int *buf, int length, mavlink_message_t *msg)
/*@
  requires
    msg::__mavlink_message<crc,_,_,_,_,_,_,_>@M
    * buf::buffer_helper<length,n,ma,n,se,sy,co,ms,f1,s1>
    * crc::_checksum<_,_>
  ensures
    msg::__mavlink_message<crc,ma,n,se,sy,co,ms,_>
    * crc::_checksum<f1,s1>
    & res = 1;
  requires
    msg::__mavlink_message<crc,_,_,_,_,_,_,_>@M
    * buf::buffer_helper<length,n,ma,n,se,sy,co,ms,f1,s1>
    * crc::_checksum<_,_>
    & n = 0
  ensures
    msg::__mavlink_message<crc,ma,n,se,sy,co,ms,_>
    * crc::_checksum<f1,s1>
    & res = 1;
  requires
    buf::int_star<ma>
    * buf1::arr_buf<buf, _, _, _, n>
    & length != n + 8
    & buf1 = buf + 1
  ensures res = 0;
*/
{
    if (buf[1] + 8 != length) {
      return 0;
    }

    msg->magic = buf[0];
    msg->len = buf[1];
    msg->seq = buf[2];
    msg->sysid = buf[3];
    msg->compid = buf[4];
    msg->msgid = buf[5];

    // msg->checksum = buf[msg->len + 7]; // if we count the bytes, this should be buf[msg->len + 6]
    msg->checksum.first = buf[msg->len + 7];
    msg->checksum.second = buf[msg->len + 8];

    // char *payload_buf = ((const char *)(&((msg)->payload[0])));
    // memcpy(payload_buf, &buf[6], msg->len);
    msg->payload = malloc(msg->len);
    memcpy(msg->payload, buf + 6, msg->len);

    return 1;
}

int parse_mavlink_msg_fixed(int *buf, int length, mavlink_message_t *msg)
/*@
  requires
    msg::__mavlink_message<crc,_,_,_,_,_,_,_>@M
    * buf::buffer_helper<length,n,ma,n,se,sy,co,ms,f1,s1>
    * crc::_checksum<_,_>
  ensures
    msg::__mavlink_message<crc,ma,n,se,sy,co,ms,_>
    * crc::_checksum<f1,s1>
    & res = 1;
  requires
    msg::__mavlink_message<crc,_,_,_,_,_,_,_>@M
    * buf::buffer_helper<length,n,ma,n,se,sy,co,ms,f1,s1>
    * crc::_checksum<_,_>
    & n = 0
  ensures
    msg::__mavlink_message<crc,ma,n,se,sy,co,ms,_>
    * crc::_checksum<f1,s1>
    & res = 1;
  requires
    buf::int_star<ma>
    * buf1::arr_buf<buf, _, _, _, n>
    & length != n + 8
    & buf1 = buf + 1
  ensures res = 0;
*/
{
    if (buf[1] + 8 != length) {
      return 0;
    }

    msg->magic = buf[0];
    msg->len = buf[1];
    msg->seq = buf[2];
    msg->sysid = buf[3];
    msg->compid = buf[4];
    msg->msgid = buf[5];

    // msg->checksum = buf[msg->len + 7]; // if we count the bytes, this should be buf[msg->len + 6]
    msg->checksum.first = buf[msg->len + 6];
    msg->checksum.second = buf[msg->len + 7];

    // char *payload_buf = ((const char *)(&((msg)->payload[0])));
    // memcpy(payload_buf, &buf[6], msg->len);
    msg->payload = malloc(msg->len);
    memcpy(msg->payload, buf + 6, msg->len);

    return 1;
}
