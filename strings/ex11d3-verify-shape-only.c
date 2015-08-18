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
     ensures emp;
  */
{
 while ((*s1++ = *s2++) != '\0')
  /*@
     requires s1::WFSeg<p>*p::char_star<0,q>*q::BADS<> * s2::WFS<> 
     ensures s1::WFSeg<ss>*ss::WFSeg<q2>*q2::char_star<0,qq>*qq::BADS<>
              * s2'::char_star<0,_> & s1'=ss;
  */
         ;    
}


