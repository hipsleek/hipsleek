/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
 */
#include <stdlib.h>

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

extern int __VERIFIER_nondet_int(void);

int (cstrcmp)(const char *s1, const char *s2)
  /*@
     requires s1::WFS<n1> * s2::WFS<n2>
     ensures true;
  */
 {
     unsigned char uc1, uc2;
     /* Move s1 and s2 to the first differing characters 
        in each string, or the ends of the strings if they
        are identical.  */
     while (*s1 != '\0' && *s1 == *s2) 
       /*@
          requires s1::WFS<n1> * s2::BADS<>
          ensures s1::WFSeg<s1',n1>*s1'::char_star<0,q1>*q1::BADS<> * s2'::BADS<>
          or s1::WFSeg<s1',m1>*s1'::char_star<c1,q>*q::WFS<n1-m1-1>*s2::WFSeg<s2',m2>*s2'::char_star<c2,qq>*qq::BADS<>;
       */
     {
         s1++;
         s2++;
     }
     /* Compare the characters as unsigned char and
        return the difference.  */
     uc1 = (*(unsigned char *) s1);
     uc2 = (*(unsigned char *) s2);
     return ((uc1 < uc2) ? -1 : (uc1 > uc2));
 }

int main() {
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
    return cstrcmp(nondetString1,nondetString2);
}
