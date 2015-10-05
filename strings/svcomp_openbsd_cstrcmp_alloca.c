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

lemma_safe self::WFS<> <-> self::WFSeg<q>*q::char_star<0,qq>*qq::BADS<>.

*/

extern int __VERIFIER_nondet_int(void);

/*
 * Compare strings.
 */

int cstrcmp(const char *s1, const char *s2)
  /*@
     requires s1::WFS<> * s2::WFS<>
     ensures true;
  */
{
  while (*s1 == *s2++)
    /*@
       requires s1::WFS<> * s2::BADS<>
       ensures eres::ret_int<0>*s1::WFSeg<q>*q::char_star<0,s1'>*s1'::BADS<> * s2'::BADS<> & flow ret_int
            or s1::WFSeg<s1'>*s1'::char_star<c1,q>*q::WFS<>*s2::WFSeg<s2'>*s2'::char_star<c2,qq>*qq::BADS<> & flow __norm
            or s1'::char_star<c1,q>*s2'::char_star<c2,qq>*qq::BADS<> & flow __norm;
    */
    if (*s1++ == 0)
      return (0);
  return (*(unsigned char *)s1 - *(unsigned char *)--s2);
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
/*==========================
#svcomp_openbsd_cstrncmp.c
to test more with double linked list
==========================*/

