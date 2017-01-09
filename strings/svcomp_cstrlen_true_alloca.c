/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
 */
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
*/

extern int __VERIFIER_nondet_int(void);

int (cstrlen)(const char *s)
 {
     const char *p = s;
     /* Loop over the data in s.  */
     while (*p != '\0')
       /*@
          requires p::WFS<> 
          ensures p::WFSeg<p'>*p'::char_star<0,q>*q::BADS<>;
       */
         p++;
     return (int)(p - s);
 }

int main() {
    int length1 = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    char* nondetString1 = (char*) alloca(length1 * sizeof(char));
    nondetString1[length1-1] = '\0';
    return cstrlen(nondetString1);
}


