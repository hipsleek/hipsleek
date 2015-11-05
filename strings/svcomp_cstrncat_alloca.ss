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
  if (n!=0){
     int y = get_char(s2);
     s2 = plus_plus_char(s2);
     write_char(s1,y);
     int x = get_char(s1);
     if (x!=0){
        n = n - 1;
        s1 = plus_plus_char(s1);
     }
  }
}
 
