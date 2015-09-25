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

void while1(ref char_star s1, ref char_star s2)
infer [P,Q,@classic,@pure_field]
  requires P(s1)*Q(s2)
  ensures true;
{
  char_star p = s1;
  char_star tmp = p;
  p = plus_plus_char(p);
  int c = get_char(tmp);
  char_star s = s2; 
  while(true)
  infer [U,@classic,@pure_field]
    requires U(s)
    ensures true;
  {
     char_star tmp = s;
     s = plus_plus_char(s);
     int x = get_char(tmp);
     write_char(s, x); 
     if (x == c){
        return;
      }
  if (x == 0)
     break;
  }
}
