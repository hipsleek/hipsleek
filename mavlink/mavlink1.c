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

pred arr_buf<root,end,size,v> == self::int_star<v> * q::arr_buf<root,end,size-1,_> & q=self+1
  inv root != null
  & root <= self <= root+size;
*/

typedef struct _checksum {
  int first;
  int second;
} checksum;

typedef struct _msg {
  checksum cs;
  int l;
  int payload[MAVLINK_MAX_PAYLOAD_LEN+MAVLINK_NUM_CHECKSUM_BYTES];
} msg;

void *memcpy(void *dest, void *src, int length) __attribute__ ((noreturn))
/*@
  requires dest=null & src = null
  ensures  true;
  requires src::arr_buf<_,_,_,_> & dest=null
  ensures  true;
  requires dest::arr_buf<_,_,_,_> & src=null
  ensures  true;
  requires dest::arr_buf<r2,e2,s2,v2> * src::arr_buf<r1,e1,s1,v1>  & length>=0 & s1>=length & s2>=length
  ensures  dest::arr_buf<r2,e2,s2,v2> * src::arr_buf<r1,e1,s1,v1> & v2 = v1;
*/;

void* cast_int(int* x)  __attribute__ ((noreturn))
/*@
  case {
    x != null -> requires  x::arr_buf<r2,e2,s2,v2>
                      ensures  res::void*<_> * res::arr_buf<r2,e2,s2,v2>;
    x = null -> requires true ensures res = null;
  }
*/;

int parse(int *buf, int len, msg *output)
/*@
  requires buf::int_star<n>
            * output::_msg<cs,l,p>@M
            * cs::_checksum<f,s>
            * buf_p::arr_buf<buf,end,n+2,_>
            * end1::int_star<f1>
            * end::int_star<s1>
            & buf_p = buf + 1
            & end1 = end-1
  ensures f = f1 & s = s1 & l = n;
*/
{
  if(buf[0] + 3 != len) {
    return 0;
  }

  output->l = buf[0];
  int p = output->payload[0];
  //@ dprint;
  void *addr_of_p = cast_int(&p);
  void *addr_inp = cast_int(buf + 1);
  memcpy(addr_of_p, addr_inp, output->l);
  output->cs.first = buf[output->l+1];
  output->cs.second = buf[output->l+2];

  return 1;
}
