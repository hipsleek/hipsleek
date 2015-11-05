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


void while1(ref char_star s1, ref char_star s2)
  requires s1::WFS<> * s2::BADS<>
  ensures s1::WFSeg<s1'>*s1'::char_star<0,q1>*q1::BADS<> * s2'::BADS<>
          or s1::WFSeg<s1'>*s1'::char_star<c1,q>*q::WFS<>*s2::WFSeg<s2'>*s2'::char_star<c2,qq>*qq::BADS<>;
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
