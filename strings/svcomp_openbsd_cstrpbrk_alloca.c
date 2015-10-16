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

lemma_safe self::WFS<> <-> self::WFSeg<q>*q::char_star<0,q2>*q2::BADS<>.

lemma_safe self::WFS<> <- self::WFSeg<q>*q::char_star<c,q2>*q2::WFS<> & c!=0.

*/

extern int __VERIFIER_nondet_int(void);

/*
 * Find the first occurrence in s1 of a character in s2 (excluding NUL).
 */
char *
cstrpbrk(const char *s1, const char *s2)
  /*@
    requires s1::WFS<>*s2::WFS<>
    ensures true;
  */
{
	const char *scanp;
	int c, sc;
	while ((c = *s1++) != 0)
          /*@
             requires s1::WFS<> * s2::WFS<>
             ensures s1::WFSeg<p>*p::char_star<0,s1'>*s1'::BADS<>;
          */
        {
		for (scanp = s2; (sc =*scanp++) != 0;)
                  /*@
                     requires scanp::WFS<>
                     ensures scanp::WFSeg<q>*q::char_star<0,scanp'>*scanp'::BADS<> & flow __norm;
                          or eres::ret_char_star<ss>*scanp::WFSeg<scanp'>*scanp'::char_star<c,q>*q::WFS<> & flow ret_char_star;
                  */;
			if (sc == c)
				return ((char *)(s1 - 1));
	}
	return (NULL);
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
    cstrpbrk(nondetString1,nondetString2);
    return 0;
}


