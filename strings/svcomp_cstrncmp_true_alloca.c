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

lemma_safe self::WFS<> -> self::BADS<>.

*/

extern int __VERIFIER_nondet_int(void);

int (cstrncmp)(const char *s1, const char *s2, int n)
  /*@
     requires s1::WFS<> * s2::WFS<>
     ensures true;
  */
 {
     unsigned char uc1, uc2;
     /* Nothing to compare?  Return zero.  */
     if (n == 0)
         return 0;
     /* Loop, comparing bytes.  */
     while (n-- > 0 && *s1 == *s2) 
       /*@
          requires s1::WFS<> * s2::BADS<> & n!=0
          ensures s1'::char_star<0,q>*q::BADS<>*s2'::char_star<0,qq>*qq::BADS<> & n' = 0 
               or s1'::char_star<c,q>*q::WFS<>*s2'::char_star<c,qq>*qq::BADS<> & n' = 0
               or s1'::char_star<0,q>*q::BADS<>*s2'::char_star<0,qq>*qq::BADS<> & n'!=0
               or s1'::char_star<0,q>*q::BADS<>*s2'::char_star<c2,qq>*qq::BADS<> & c2 != 0
               or s1'::char_star<c1,q>*q::BADS<>*s2'::char_star<c2,qq>*qq::BADS<>
               or s1::WFSeg<s1'>*s1'::WFS<>*s2::WFSeg<s2'>*s2'::BADS<> & n' > 0;
               
          //s1::WFSeg<s1'>*s1'::char_star<0,q1>*q1::BADS<> * s2'::BADS<>
          //or s1::WFSeg<s1'>*s1'::char_star<c1,q>*q::WFS<>*s2::WFSeg<s2'>*s2'::char_star<c2,qq>*qq::BADS<>
          //or s1::WFSeg<s1'>*s1'::char_star<_,q>*q::WFS<>*s2::WFSeg<s2'>*s2'::char_star<_,qq>*qq::BADS<> & n' = 0;
       */
     {
         /* If we've run out of bytes or hit a null, return zero
            since we already know *s1 == *s2.  */
         if (n == 0 || *s1 == '\0')
             return 0;
         s1++;
         s2++;
         /*@dprint;*/
     }
     uc1 = (*(unsigned char *) s1);
     uc2 = (*(unsigned char *) s2);
     return ((uc1 < uc2) ? -1 : (uc1 > uc2));
 }

/*int main() {
    int length1 = __VERIFIER_nondet_int();
    int length2 = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    if (length2 < 1) {
        length2 = 1;
    }
    char* nondetString1 = (char*) alloca(length1 * sizeof(char));
    char* nondetString2 = (char*) alloca(length2 * sizeof(char));
    nondetString1[length1-1] = '\0';
    nondetString2[length2-1] = '\0';
    return cstrncmp(nondetString1,nondetString2,__VERIFIER_nondet_int());
}

*/
