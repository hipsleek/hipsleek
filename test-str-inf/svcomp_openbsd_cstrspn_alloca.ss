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

void while1(ref char_star s, int c)
infer [P,@classic,@pure_field]
  requires P(s)
  ensures true;
{
  char_star ss = s;
  s = plus_plus_char(s);
  int x = get_char(ss);
  if (x != 0){
     if (x == c)
        return;
     while1(s, c);
  }
}
