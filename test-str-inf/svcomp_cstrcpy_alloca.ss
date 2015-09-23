pred_prim Dangling<>
inv true;

WFS<> ==
  self::char_star<0,q>*q::BADS<> 
  or self::char_star<v,q>*q::WFS<> & v!=0 
  inv true;

WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;

HeapPred P(char_star x).
HeapPred Q(char_star x).
void while1(ref char_star dst, ref char_star src)
infer [P,Q,@classic,@pure_field]
  requires P(dst)*Q(src)
  ensures true;
{
  char_star s = dst;
  int y = get_char(src);
  dst = plus_plus_char(dst);
  src = plus_plus_char(src); 
  write_char(s, y);
  int x = get_char(s);
  if (x!=0) {
    while1(dst, src);
  }
}
