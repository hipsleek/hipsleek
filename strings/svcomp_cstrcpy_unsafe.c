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

char* new_str()
  /*@
     requires emp
     ensures res::WFS<>;
  */
 {}

char *(cstrcpy)(char *s1, const char *s2)
  /*@
    requires s1::WFS<> * s2::WFS<>
    ensures s2::WFSeg<q>*q::char_star<0,qq>*qq::BADS<>;
  */
 {
     char *dst = s1;
     const char *src = s2;
     /* Do the copying in a loop.  */
     while ((*s1++ = *s2++) != '\0')
       /*@
          requires s1::WFS<> * s2::WFS<>
          ensures s2::WFSeg<qq>*qq::char_star<0,s2'>*s2'::BADS<> * s1::WFSeg<q>*q::char_star<0,s1'>*s1'::WFS<>;
       */
         ;               /* The body of this loop is left empty. */
     /* Return the destination string.  */
     return s1;
 }

int main()
  /*@
     requires true
     ensures res=0;
  */ 
{
  char* s2 = new_str();
  char* s1 = new_str();
  cstrcpy(s1, s2);
  return 0;
}
  
