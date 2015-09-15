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

int
cstrncmp(const char *s1, const char *s2, size_t n)
  /*@
     requires s1::WFS<> * s2::WFS<>
     ensures true;
  */
{

	if (n == 0)
		return (0);
	do 
          /*@
             requires s1::WFS<> * s2::WFS<>
             ensures s1::WFSeg<q>*q::char_star<0,s1'>*s1'::BADS<> & flow __norm
                  or n' = 0 & flow __norm
                  or eres::ret_int<p>*s1::WFSeg<s1'>*s1'::char_star<c1,q>*q::BADS<>*s2::WFSeg<qq>*qq::char_star<c2,s2'>*s2'::BADS<> & flow ret_int;
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

