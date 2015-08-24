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

char *(cstrcpy)(char *s1, const char *s2)
 {
     char *dst = s1;
     const char *src = s2;
     /* Do the copying in a loop.  */
     while ((*dst++ = *src++) != '\0')
         ;               /* The body of this loop is left empty. */
     /* Return the destination string.  */
     return s1;
 }

char* new_str()
  /*@
     requires emp
     ensures res::WFS<>;
  */
 {}

int main()
  /*@
     requires true
     ensures res=0;
  */ 
{
  char* s2;
  char* s1;
  cstrcpy(s1, s2);
  return 0;
}
  
