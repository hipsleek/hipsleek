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
HeapPred U(char_star x).

void while1(ref char_star s)
infer [P,@classic,@pure_field]
  requires P(s)
  ensures true;
{
  int x=get_char(s);
  if (x!=0) {
    s = plus_plus_char(s);
    while1(s);
  }
}

void while2(ref char_star s1, ref char_star s2, int n)
infer [U,Q,@classic,@pure_field]
  requires U(s1)*Q(s2)
  ensures true;
{
  char_star tmp = s2;
  s2 = plus_plus_char(s2);
  int x = get_char(tmp);
  write_char(s1,x);
  if (x == 0)
     return;
  s1 = plus_plus_char(s1);
  n = n - 1;
  if (n == 0)
    return;
  while2(s1,s2,n);
}
 
