/*@
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
*/


void while2(char* s1,char* s2)
  /*@
     requires s1::char_star<0,q1>*q1::BADS<> * s2::WFS<> 
     ensures s2::WFSeg<ss>*ss::char_star<0,qq>*qq::BADS<>;
  */
{
 while (*s2!= '\0')
  /*@
     requires s1::char_star<_,q> * q::BADS<> * s2::WFS<> 
     ensures s1'::char_star<_,q2> * q2::BADS<> * s2::WFSeg<s2'>*s2'::char_star<0,qq>*qq::BADS<>;
  */
  {
     *s1 = *s2;
     s1++;
     s2++;
  }    
}


