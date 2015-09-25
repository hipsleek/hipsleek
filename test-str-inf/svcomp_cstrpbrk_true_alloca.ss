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
  char_star sc1 = s1;
  int c = get_char(sc1);
  if (c != 0){
     char_star s = s2; 
     while2(s,c);
     if (get_char(s) != c){
     	return;   
     }
     sc1 = plus_plus_char(sc1);
     while1(s1,s2);
  }
}

void while2(ref char_star s, int c)
infer [U,@classic,@pure_field]
  requires U(s)
  ensures true;
{
  int x = get_char(s);
  if (x != 0){
     if (x != c){
        s = plus_plus_char(s);
        while2(s,c);
     }
  }
}
