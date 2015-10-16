#include <stdlib.h>

/*@
WFS<n> ==
  self::char_star<0,q>*q::BADS<> & n=1
  or self::char_star<v,q>*q::WFS<n-1> & v!=0 
  inv n>=1;

WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;

lemma_safe self::WFS<n> -> self::BADS<>.
*/

extern int __VERIFIER_nondet_int(void);

char *(cstrncpy)(char *s1, const char *s2, int n)
/*@
    requires s1::BADS<> * s2::WFS<l> & n > 0
    ensures true;
*/
 {
     char *dst = s1;
     const char *src = s2;
     /* Copy bytes, one at a time.  */
     while (n > 0)
        /*
          ensures src::WFSeg<qq>*qq::char_star<0,src'>*src'::BADS<> * dst::WFSeg<pp>*pp::char_star<0,dst'>*dst'::BADS<> 
               or src::WFSeg<src'>*src'::WFS<_> * dst::WFSeg<dst'>*dst'::BADS<>;
        */
       /*@
          requires dst::BADS<> * src::WFS<l> & n>=0
          case {
            n>=l -> ensures src::WFSeg<qq>*qq::char_star<0,src'>*src'::BADS<> * dst::WFSeg<pp>*pp::char_star<0,dst'>*dst'::BADS<> & n'=n-l;
            n<l -> ensures src::WFSeg<src'>*src'::WFS<l-n> * dst::WFSeg<dst'>*dst'::BADS<> & n'=0;
          }          
       */
     {
         n--;
         if ((*dst++ = *src++) == '\0')
             break;
     }
     return s1;
 }

