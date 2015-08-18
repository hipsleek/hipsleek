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

void while1(char* s)
  /*@
    requires s::WFS<> 
    ensures s::WFSeg<p>*p::char_star<0,q>*q::BADS<>;
  */
{ 
  while (*s!='\0') 
  /*@
     requires s::WFS<> 
     ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>;
  */
  {
    s++;
  }
}

void while2(char* s1,char* s2)
  /*@
    requires s1::char_star<_,q>*q::BADS<> * s2::WFS<> 
    ensures s1::WFSeg<q2>*q2::char_star<0,qq>*qq::BADS<>;
            //* s2::char_star<0,_> & s1=q2; 
  */
{
  while ((*s1++ = *s2++) != '\0')
     /*@
        requires s1::char_star<_,q>*q::BADS<> * s2::WFS<> 
        ensures s1::WFSeg<q2>*q2::char_star<0,qq>*qq::BADS<> 
                * s2'::char_star<0,_> & s1'=q2; 
     */
         ;
  /*@dprint;*/
}

