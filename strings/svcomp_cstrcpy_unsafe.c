/*@
WFS<n> ==
  self::char_star<0,q>*q::BADS<> & n=0
  or self::char_star<v,q>*q::WFS<n-1> & v!=0 
  inv n>=0;

WFSeg<p, n> ==
  self=p & n=0
  or self::char_star<v,q>*q::WFSeg<p, n-1> & v!=0
  inv n>=0;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;

lemma_safe self::WFS<n> -> self::BADS<>.
*/

char *(cstrcpy)(char *s1, const char *s2)
  /*@
    requires s1::BADS<> * s2::WFS<n2>
    ensures s1::WFSeg<pp,n1>*pp::char_star<0,_> & res=s1;
  */
 {
     char *dst = s1;
     const char *src = s2;
     /* Do the copying in a loop.  */
     while ((*dst++ = *src++) != '\0')
     /*@
          requires dst::BADS<> * src::WFS<n2>
          ensures src::WFSeg<qq,n2>*qq::char_star<0,src'>*src'::BADS<> * dst::WFSeg<pp,n1>*pp::char_star<0,dst'>*dst'::BADS<>;
       */
       {
       } 
         ;               /* The body of this loop is left empty. */
     /* Return the destination string.  */
     return s1;
 }

char* new_str()
  /*@
     requires emp
     ensures res::WFS<n>;
  */
 {}

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
  
