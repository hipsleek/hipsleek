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

void while1(ref char_star s1, ref char_star s2, int n)
infer [P,Q,@classic,@pure_field]
  requires P(s1)*Q(s2)
  ensures true;
{
  if (n > 0){
     n = n - 1;
     char_star tmp1 = s1;
     char_star tmp2 = s2;
     s1 = plus_plus_char(s1); 
     s2 = plus_plus_char(s2);
     int x = get_char(tmp2);
     write_char(tmp1,x);
     if (x == 0){
        char_star ss = s1;
        int n2 = n;
        while2(ss,n2);
        return;
     }
     while1(s1,s2,n);
  }
}

void while2(ref char_star s, int n)
infer [U,@classic,@pure_field]
  requires U(s)
  ensures true;
{
  int tmp = n;
  n = n-1;
  if (tmp == 0)
    return;
  char_star tmp_s = s;
  s = plus_plus_char(s);
  write_char(tmp_s, 0);
  while2(s, n);
}
