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
#define MAVLINK_MAX_PAYLOAD_LEN 255
#define MAVLINK_NUM_CHECKSUM_BYTES 2

/*@
//pred arr_seg<p,n> == self::arr_int<_>*q::arr_seg<p,n-1> & q=self+1
//     or self=p & n=0
//  inv n>=0 & p=self+n;
//
//pred_prim strbuf<hd,bsize,sl:int,zeroflag:bool>
//  inv hd != null // hd is non-null root ptr
//   & hd <= self <= hd+bsize;

pred arr_buf<root,end,max_size,size,v> == self::int_star<v> * q::arr_buf<root,end,max_size,size-1,_> & q=self+1
  or self::int_star<v> & self=end & size = 1
  inv root <= self <= end
  & end - root + 1 = max_size
  &  1 <= size <= max_size;
*/

typedef struct _checksum {
  int first;
  int second;
} checksum;

typedef struct _msg {
  checksum cs;
  int l;
  int *payload;
  //int payload[MAVLINK_MAX_PAYLOAD_LEN+MAVLINK_NUM_CHECKSUM_BYTES];
} msg;

void *memcpy(int *dest, int *src, int length) __attribute__ ((noreturn))
/*@
  requires dest=null & src = null
  ensures  true;
  requires src::arr_buf<_,_,_,_,_> & dest=null
  ensures  true;
  requires dest::arr_buf<_,_,_,_,_> & src=null
  ensures  true;
  requires dest::arr_buf<r2,e2,m2,s2,v2> * src::arr_buf<r1,e1,m1,s1,v1>  & length>=0 & s1>=length & s2>=length
  ensures  dest::arr_buf<r2,e2,m2,s2,v1> * src::arr_buf<r1,e1,m1,s1,v1>;
*/;

int* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::arr_buf<r,e,m,s,v> & s=size;
  }
*/;

// int simple(int *buf, int length)
// /*@
//   requires buf::arr_buf<buf, end, length, length-1,_> * end::int_star<v> & length > 0
//   ensures res = v;
// */
// {
//   int k = buf[length - 1];

//   //@ dprint;
//   return k;
// }

int parse_buggy(int *buf, int length, msg *output)
/*@
  requires
    output::_msg<crc,l,p>@M
    * buf::int_star<n>
    * buf1::arr_buf<buf, end, length, n, _>
    * crc::_checksum<f,s>
    * end1::int_star<f1>
    * end::int_star<s1>
    & end1 = end - 1
    & length = n + 3
    & buf1 = buf + 1
  ensures
    output::_msg<crc, n, _>
    * crc::_checksum<f1,s1>
    & res = 1;
  requires
    output::_msg<crc,l,p>@M
      * buf::int_star<n>
      * crc::_checksum<f,s>
      * end1::int_star<f1>
      * end::int_star<s1>
      & end1 = end - 1
      & length = n + 3
      & end1 = buf + 1
      & n = 0
  ensures
    output::_msg<crc, n, _>
    * crc::_checksum<f1,s1>
    & res = 1;
  requires
    buf::int_star<n>
    * buf1::arr_buf<buf, _, _, _, _>
    & length != n + 3
    & buf1 = buf + 1
  ensures res = 0;
*/
{
  if(buf[0] + 3 != length) {
    return 0;
  }

  output->l = buf[0];

  output->cs.first = buf[output->l + 2];
  output->cs.second = buf[output->l + 3];

  int *inp = buf + 1;
  output->payload = malloc(output->l);
  memcpy(output->payload, inp, output->l);

  return 1;
}

int parse(int *buf, int length, msg *output)
/*@
  requires
    output::_msg<crc,l,p>@M
    * buf::int_star<n>
    * buf1::arr_buf<buf, end, length, n, _>
    * crc::_checksum<f,s>
    * end1::int_star<f1>
    * end::int_star<s1>
    & end1 = end - 1
    & length = n + 3
    & buf1 = buf + 1
  ensures
    output::_msg<crc, n, _>
    * crc::_checksum<f1,s1>
    & res = 1;
  requires
    output::_msg<crc,l,p>@M
      * buf::int_star<n>
      * crc::_checksum<f,s>
      * end1::int_star<f1>
      * end::int_star<s1>
      & end1 = end - 1
      & length = n + 3
      & end1 = buf + 1
      & n = 0
  ensures
    output::_msg<crc, n, _>
    * crc::_checksum<f1,s1>
    & res = 1;
  requires
    buf::int_star<n>
    * buf1::arr_buf<buf, _, _, _, _>
    & length != n + 3
    & buf1 = buf + 1
  ensures res = 0;
*/
{
  if(buf[0] + 3 != length) {
    return 0;
  }

  output->l = buf[0];

  output->cs.first = buf[output->l + 1];
  output->cs.second = buf[output->l + 2];

  int *inp = buf + 1;
  output->payload = malloc(output->l);
  memcpy(output->payload, inp, output->l);

  return 1;
}
