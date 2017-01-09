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

lemma_safe self::WFSeg<p> <- self::WFSeg<q>*q::WFSeg<p> .

lemma_safe self::WFS<> <-> self::WFSeg<q>*q::char_star<0,q2>*q2::BADS<> .

*/

extern int __VERIFIER_nondet_int(void);

/*
 * Concatenate src on the end of dst.  At most strlen(dst)+n+1 bytes
 * are written at dst (at most n+1 bytes being appended).  Return dst.
 */
char *cstrncat(char *dst, const char *src, size_t n)
  /*@
     requires dst::WFS<> * src::WFS<> & n!= 0
     ensures res=dst;
  */
{
	if (n != 0) {
		char *d = dst;
		const char *s = src;

		while (*d != 0)
                  /*@
                     requires d::WFS<>
                     ensures d::WFSeg<d'>*d'::char_star<0,q>*q::BADS<>;
                  */
			d++;
		do
                  /*@
          	     requires d::char_star<_,q> * q::BADS<> * s::WFS<>
          	     ensures s::WFSeg<qq>*qq::char_star<0,s'>*s'::BADS<> * d::WFSeg<d'>*d'::char_star<0,q2>*q2::BADS<>
                          or d::WFSeg<d'>*d'::BADS<> & n' = 0;
                  */
                {
			if ((*d = *s++) == 0)
				break;
			d++;
		} while (--n != 0);
		*d = 0;
	}
	return (dst);
}

int main() 
  /*@
     requires true
     ensures res = 0;
  */
{
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
