
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

char *(cstrcat)(char *s1, const char *s2)
 /*@
    requires s1::WFS<> * s2::WFS<> 
    ensures res::WFSeg<s>*s::WFSeg<x>*x::char_star<0,qq>*qq::BADS<>;
 */

 {
     char *s = s1;
     while (*s != '\0')
       /*@
          requires s::WFS<> 
          ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>;
       */
         s++;
     while ((*s++ = *s2++) != '\0')
       /*@
          requires s::char_star<_,q>*q::BADS<> * s2::WFS<> 
          ensures s::WFSeg<q2>*q2::char_star<0,qq>*qq::BADS<> 
                  * s2'::char_star<0,_> & s'=q2; 
       */
         ;               
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
  char *s1 = new_str();
  char *s2 = new_str();
  cstrcat(s1, s2);
  return 0;
}

