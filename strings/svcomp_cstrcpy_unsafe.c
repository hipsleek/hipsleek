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

lemma_safe self::WFS<> -> self::BADS<>.
*/

char *(cstrcpy)(char *s1, const char *s2)
  /*@
    requires s1::WFS<> * s2::WFS<>
    ensures s1::WFSeg<pp>*pp::char_star<0,_> & res=s1;
  */
 {
     char *dst = s1;
     const char *src = s2;
     /* Do the copying in a loop.  */
     while ((*dst++ = *src++) != '\0')
     /*@
          requires dst::BADS<> * src::WFS<>  //dst can be anything
          ensures src::WFSeg<qq>*qq::char_star<0,src'>*src'::BADS<> * dst::WFSeg<pp>*pp::char_star<0,dst'>*dst'::BADS<>;
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
     ensures res::WFS<>;
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
  
