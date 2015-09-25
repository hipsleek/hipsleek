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

void while1(ref char_star s, int n)
infer [P,@classic,@pure_field]
  requires P(s)
  ensures true;
{ 
  if (n!=0)
    if (get_char(s) != 0){
      n = n-1;
      s = plus_plus_char(s);
      while1(s,n);
    }
}
