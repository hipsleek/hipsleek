#include <stdlib.h>

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

extern int __VERIFIER_nondet_int(void);

char *(cstrcpy)(char *s1, const char *s2)
/*@
    requires s1::BADS<> * s2::WFS<>
    ensures s1::WFSeg<pp>*pp::char_star<0,_> & res=s1;
*/
{
     char *dst = s1;
     const char *src = s2;
     /* Do the copying in a loop.  */
     while ((*dst++ = *src++) != '\0')
       /*@
          requires dst::BADS<> * src::WFS<>
          ensures src::WFSeg<qq>*qq::char_star<0,src'>*src'::BADS<> * dst::WFSeg<pp>*pp::char_star<0,dst'>*dst'::BADS<>;
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
  int length1 = __VERIFIER_nondet_int();
  int length2 = __VERIFIER_nondet_int();
  if (length1 < 1) {
      length1 = 1;
  }
  if (length2 < 1) {
      length2 = 1;
  }
  if (length1 < length2) return 0;
  char* nondetArea = (char*) alloca(length1 * sizeof(char));
  char* nondetString = (char*) alloca(length2 * sizeof(char));
  nondetString[length2-1] = '\0';
  cstrcpy(nondetArea,nondetString);
  return 0;
}
  
