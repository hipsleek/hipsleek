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

int
cstrncmp(const char *s1, const char *s2, size_t n)
  /*@
     requires s1::WFS<n1> * s2::WFS<n2>
     ensures true;
  */
{

	if (n == 0)
		return (0);
	do 
          /*@
             requires s1::WFS<n1> * s2::WFS<n2>
             ensures s1::WFSeg<q,n1>*q::char_star<0,s1'>*s1'::BADS<> & flow __norm
               or n' = 0 & flow __norm
               or eres::ret_int<p>*s1::WFSeg<s1',n1>*s1'::char_star<c1,q>*q::BADS<>*s2::WFSeg<qq,n2>*qq::char_star<c2,s2'>*s2'::BADS<> & flow ret_int;
          */
        {
          if (*s1 != *s2++)
             return (*(unsigned char *)s1 - *(unsigned char *)--s2);
          if (*s1++ == 0)
	     break;
	} while (--n != 0); 
	return (0);
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
    return cstrncmp(nondetString1,nondetString2,__VERIFIER_nondet_int());
}
/*==========================
#svcomp_openbsd_cstrncmp.c
to test with double linked list
==========================*/

