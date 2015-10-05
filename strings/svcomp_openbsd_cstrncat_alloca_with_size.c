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

/*
 * Concatenate src on the end of dst.  At most strlen(dst)+n+1 bytes
 * are written at dst (at most n+1 bytes being appended).  Return dst.
 */
char *cstrncat(char *dst, const char *src, size_t n)
  /*@
     requires dst::WFS<n1> * src::WFS<n2> & n!= 0
     ensures res=dst;
  */
{
	if (n != 0) {
		char *d = dst;
		const char *s = src;

		while (*d != 0)
                  /*@
                     requires d::WFS<n1>
                     ensures d::WFSeg<d',n1>*d'::char_star<0,q>*q::BADS<>;
                  */
			d++;
		do
                  /*@
          	     requires d::char_star<_,q> * q::BADS<> * s::WFS<n2>
          	     ensures s::WFSeg<qq,n2>*qq::char_star<0,s'>*s'::BADS<> * d::WFSeg<d',n1>*d'::char_star<0,q2>*q2::BADS<>
                          or d::WFSeg<d',n1>*d'::BADS<> & n' = 0;
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
