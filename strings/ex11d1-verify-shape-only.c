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
int main()
  /*@
     requires true
     ensures res=0;
  */ 
{
  char *s1 = new_str();
  char *s2 = new_str();
  //while1(s1);
  while (*s1!='\0') 
  /*@
     requires s1::WFS<> 
     ensures s1::WFSeg<s1'>*s1'::char_star<0,q>*q::BADS<>;
  */
  {
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
  return 0;
}



/*==================================================

# ex11d1.c (FIXED)

  Why post-condition of 2nd loop cannot be derived?



Pass-by-value parameters should not be primed, so how can we put the right specifications?

ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>;

ERROR: at ex11d-verify-shape-only.c_21:12_21:53
Message: Pass-by-value parameters and local variables can not escape out of scope: [(s,')]

!!! **main.ml#1180:WARNING : Logging not done on finalizeStop z3... 0 invocations caught

Exception occurred: Failure("Pass-by-value parameters and local variables can not escape out of scope: [(s,')]")
*/
