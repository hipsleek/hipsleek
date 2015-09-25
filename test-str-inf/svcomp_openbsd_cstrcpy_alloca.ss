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

void while1(ref char_star t, ref char_star from)
infer [P,Q,@classic,@pure_field]
  requires P(t)*Q(from)
  ensures true;
{
  int x = get_char(from);
  write_char(t, x);
  if (x != 0){
     from = plus_plus_char(from);
     t = plus_plus_char(t);
     while1(t,from);
  }
}
