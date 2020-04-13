#define MAVLINK_MAX_PAYLOAD_LEN 255 ///< Maximum payload length
#define MAVLINK_NUM_CHECKSUM_BYTES 2

typedef unsigned short xm_u16_t;

typedef struct __mavlink_message {
  int *checksum;
  //xm_u16_t checksum; ///< sent at end of packet
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
pred_prim strbuf<hd,bsize,sl:int,zeroflag:bool>
  inv hd != null // hd is non-null root ptr
   & hd <= self <= hd+bsize
   & (!zeroflag | (zeroflag & self <= hd+sl & 0 <= sl < bsize)) // string length should exclude 0

pred mavlink_buf<ma,l,se,sy,co,ms,p,crc,ma1,n,se1,sy1,co1,ms1>
  == ma::memLoc<_,1>
    * l::memLoc<_,1>
    * l::int_star<n>
    * se::memLoc<_,1>
    * sy::memLoc<_,1>
    * co::memLoc<_,1>
    * ms::memLoc<_,1>
    * p::memLoc<_,n>
    * crc::memLoc<_,2>
    * ma::int_star<ma1>
    * se::int_star<se1>
    * sy::int_star<sy1>
    * co::int_star<co1>
    * ms::int_star<ms1>
    & self = ma
    & l = ma + 1
    & se = l + 1
    & sy = se + 1
    & co = sy + 1
    & ms = co + 1
    & p = ms + 1
    & crc = p + n
  inv 0 <= n <= 255;
*/

void *memcpy(void* dest, void* src, int n)  __attribute__ ((noreturn))
/*@
  requires dest=null & src = null
  ensures  true;
  requires src::memLoc<h2,s2> & dest=null
  ensures  true;
  requires dest::memLoc<h2,s2> & src=null
  ensures  true;
  requires dest::memLoc<h1,s1> * src::memLoc<h2,s2>  & n>=0 & s1>=n & s2>=n
  ensures  dest::memLoc<h1,s1> * src::memLoc<h2,s2> & h1 & h2;
*/;

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::memLoc<h,s> & h & s=size;
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

int parse_mavlink_msg(char *buf, int len, mavlink_message_t *msg)
{
    if (buf[1] + 8 != len)
        return 0;
    msg->magic = buf[0];
    msg->len = buf[1];
    msg->seq = buf[2];
    msg->sysid = buf[3];
    msg->compid = buf[4];
    msg->msgid = buf[5];
    msg->checksum = buf[msg->len + 7];
    char *payload_buf = ((const char *)(&((msg)->payload[0])));
    memcpy(payload_buf, &buf[6], msg->len);
    return 1;
}

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

int parse_mavlink_msg1(int *buf, int len, mavlink_message_t *msg)
/*@
  requires msg::__mavlink_message<crc,magic,length,seq,sysid,compid,msgid,payl>@M
            * buf::mavlink_buf<ma,l,se,sy,co,ms,p,ch,ma1,n,se1,sy1,co1,ms1>
  ensures magic = ma1
          & length = n
          & seq = se1
          & sysid = sy1
          & compid = co1
          & msgid = ms1;
*/
{
    if (buf[1] + 8 != len) {
      return 0;
    }

    msg->magic = buf[0];
    msg->len = buf[1];
    msg->seq = buf[2];
    msg->sysid = buf[3];
    msg->compid = buf[4];
    msg->msgid = buf[5];
    // msg->checksum = buf[msg->len + 7]; // if we count the bytes, this should be buf[msg->len + 6]
    msg->checksum = malloc(2);
    void *checksum_buf = cast_int(msg->checksum);
    //@ dprint;
    void *c = cast_int(&buf[msg->len + 6]);
    memcpy(checksum_buf, c, 2);

    void *payload_buf = cast_int(msg->payload);
    void *p = cast_int(&buf[6]);
    memcpy(payload_buf, p, msg->len);
    return 1;
}
