
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

int main() 
{  
  char* s;
  /*@ assume s'::char_star<_,_>;*/
  /*@ dprint;*/
  while (*s != '\0')
  /*@
     requires s::WFS<>
     ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>;
  */
  s++;
  return 0;
}

