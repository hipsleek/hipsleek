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
  char_star tmp2 = s2; 
  s2 = plus_plus_char(s2);
  if (get_char(s1)!=get_char(tmp2))
    return;
  char_star tmp1 = s1;
  s1 = plus_plus_char(s1);
  if (get_char(tmp1) == 0)
    return;
  n = n-1;
  if (n==0)
    return;
  while1(s1,s2,n);
}
