WFS<n> ==
  self::char_star<0,q>*q::BADS<> & n=0
  or self::char_star<v,q>*q::WFS<n-1> & v!=0 
  inv n>=0;

WFSeg<p, n> ==
  self=p & n=0
  or self::char_star<v,q>*q::WFSeg<p, n-1> & v!=0
  inv n>=0;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;

lemma_safe self::WFS<n> -> self::BADS<>.


void while1(ref char_star s1, ref char_star s2)
  requires s1::WFS<n1> * s2::BADS<>
  ensures s1::WFSeg<s1',n1>*s1'::char_star<0,q1>*q1::BADS<> * s2'::BADS<>
          or s1::WFSeg<s1',m1>*s1'::char_star<c1,q>*q::WFS<n1-m1-1>*s2::WFSeg<s2',m2>*s2'::char_star<c2,qq>*qq::BADS<>;
{
  int x=get_char(s1);
  if (x!=0) {
    int y = get_char(s2);
    if (y==x){
       s1 = plus_plus_char(s1);
       s2 = plus_plus_char(s2); 
       while1(s1,s2);
    }
  }
}
