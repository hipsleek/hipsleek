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
  s++;
  if (*s != '\0')
     while1(s);
}

void while2(char* s1,char* s2)
  /*@
     requires s1::char_star<_,q> * q::BADS<> * s2::WFS<> 
     ensures s1::char_star<_,q2> * q2::BADS<> * s2::WFSeg<ss>*ss::char_star<0,qq>*qq::BADS<>;
  */
{
  *s1 = *s2;
  s1++;
  s2++;
  if (*s2 != '\0')
     while2(s1,s2);
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
  while1(s1);
  /*@dprint;*/
  while2(s1, s2);
  return 0;
}

