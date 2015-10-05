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

lemma_safe self::WFSeg<p,n1+n2> <- self::WFSeg<q,n1>*q::WFSeg<p,n2>.

lemma_safe self::WFS<n> <-> self::WFSeg<q,n>*q::char_star<0,q2>*q2::BADS<> .

*/

extern int __VERIFIER_nondet_int(void);

char *(cstrncat)(char *s1, const char *s2, int n)
  /*@
     requires s1::WFS<n1> * s2::WFS<n2> & n!= 0
     ensures res = s1;
  */
 {
     char *s = s1;
     /* Loop over the data in s1.  */
     while (*s != '\0')
       /*@
          requires s::WFS<n1> 
          ensures s::WFSeg<s',n1>*s'::char_star<0,q>*q::BADS<>;
       */
         s++;
     /* s now points to s1's trailing null character, now copy
        up to n bytes from s1 into s stopping if a null character
        is encountered in s2.
        It is not safe to use strncpy here since it copies EXACTLY n
        characters, NULL padding if necessary.  */
     while (n != 0 && (*s = *s2++) != '\0')
       /*@
          requires s::char_star<_,q> * q::BADS<> * s2::WFS<n2>
          ensures s2::WFSeg<qq,n2>*qq::char_star<0,s2'>*s2'::BADS<> * s::WFSeg<s',n1>*s'::char_star<0,q2>*q2::BADS<>
               or s::WFSeg<s',n1>*s'::BADS<> & n' = 0;
       */
     {
         n--;
         s++;
     }
     if (*s != '\0')
         *s = '\0';
     return s1;
 }

int main() {
    int length1 = __VERIFIER_nondet_int();
    int length2 = __VERIFIER_nondet_int();
    int n = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    if (length2 < 1) {
        length2 = 1;
    }
    if (n < 1) {
        n = 1;
    }
    if (length1 < n || length1 - n < length2) return 0;
    char* nondetString1 = (char*) alloca(length1 * sizeof(char));
    char* nondetString2 = (char*) alloca(length2 * sizeof(char));
    nondetString1[length1-n-1] = '\0';
    nondetString2[length2-1] = '\0';
    cstrncat(nondetString1, nondetString2, n);
    return 0;
}
