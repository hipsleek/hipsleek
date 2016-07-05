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

WFSem<p> ==
  self=p
  or self::char_star<v,q>*q::WFSem<p> & v=0
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
    ensures res=s1;
*/
 {
     char *dst = s1;
     const char *src = s2;
     char *us;
     int n2;
     /* Copy bytes, one at a time.  */
     while (n > 0)
       /*@
          requires dst::BADS<> * src::WFS<l> & n>=0
          case {
            n >= l -> ensures src::WFSeg<qq> * qq::char_star<0,src'> * src'::BADS<> * dst::WFSeg<pp> * pp::char_star<0,dst'> * dst'::WFSem<pp2> * pp2::BADS<> & n' = n-l; 
            n < l -> ensures n' = 0;
          }
       */
     {
         n--;
         if ((*dst++ = *src++) == '\0') {
             /* If we get here, we found a null character at the end
                of s2, so use memset to put null bytes at the end of
                s1.  */
             us = dst;
             n2 = n;
             while (n2-- != 0)
               /*@
                  requires us::BADS<> & n2>=0
                  ensures us::WFSem<us'>*us'::BADS<> & n2' = -1;
               */
                {
                 *us++ = '\0';
                }
             break;
         }
     }
     return s1;
 }

int main() {
  int length = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  if (length < 1) {
      length = 1;
  }
  if (n < 1) {
      n = 1;
  }
  char* nondetArea = (char*) alloca(n * sizeof(char));
  char* nondetString = (char*) alloca(length * sizeof(char));
  nondetString[length-1] = '\0';
  cstrncpy(nondetArea, nondetString, n);
  return 0;
}
