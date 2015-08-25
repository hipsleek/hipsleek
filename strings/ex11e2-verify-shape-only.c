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
    requires s1::char_star<_,q>*q::BADS<> * s2::WFS<> 
    ensures s1::WFSeg<q2>*q2::char_star<0,qq>*qq::BADS<>; 
  */
{
 while ((*s1++ = *s2++) != '\0')
  /*@
    requires s1::char_star<_,q>*q::BADS<> * s2::WFS<> 
    ensures s1::WFSeg<s1'>*s1'::char_star<0,qq>*qq::BADS<> 
      * s2'::char_star<0,_>; 
  */
         ;    
}



/*
# ex11a2.ss

# Has the code been translated correctly?

*/
