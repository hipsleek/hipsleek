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

void while1(ref char_star s1, ref char_star s2, int n)
infer [P,Q,@classic,@pure_field]
  requires P(s1)*Q(s2)
  ensures true;
{
  int tmp = n;
  n = n - 1;
  if (tmp > 0){ 
     if (get_char(s1) == get_char(s2)) { 
        if (n == 0)
           return;
        if (get_char(s1) == 0)
           return;
        s1 = plus_plus_char(s1);
        s2 = plus_plus_char(s2);
     }
  }
}
