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

char *(cstrncpy)(char *s1, const char *s2, int n)
/*@
    requires s1::BADS<> * s2::WFS<> & n > 0
    ensures true;
*/
 {
     char *dst = s1;
     const char *src = s2;
     /* Copy bytes, one at a time.  */
     while (n > 0)
       /*@
          requires dst::BADS<> * src::WFS<> & n>=0
          ensures src::WFSeg<qq>*qq::char_star<0,src'>*src'::BADS<> * dst::WFSeg<pp>*pp::char_star<0,dst'>*dst'::BADS<>
               or n' = 0;
               //or src::WFSeg<src'>*src'::BADS<> * dst::WFSeg<dst'>*dst'::BADS<>;
       */
     {
         n--;
         if ((*dst++ = *src++) == '\0')
         {
             break;

         }
     }
     return s1;
 }

