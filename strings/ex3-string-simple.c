
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
    ensures s2::WFSeg<q>*q::char_star<0,qq>*qq::BADS<>;
 */

 {
  while (*s1!='\0') 
  /*@
     requires s1::WFS<> 
     ensures s1::WFSeg<s1'>*s1'::char_star<0,q>*q::BADS<>;
  */
  {
   /*@dprint;*/
    s1++;
  }
  //while2(s1, s2);
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

