#include <stdlib.h>

/*@
WFS<n> ==
  self::char_star<0,q>*q::BADS<> & n=1
  or self::char_star<v,q>*q::WFS<n-1> & v!=0 
  inv n>=1;

WFSeg<p> ==
  self=p
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

WFSem<p> ==
  self=p
  or self::char_star<v,q>*q::WFSem<p> & v=0
  inv true;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;

lemma_safe self::WFS<n> -> self::BADS<>.

*/

extern int __VERIFIER_nondet_int(void);

/*
 * Copy src to dst, truncating or null-padding to always copy n bytes.
 * Return dst.
 */
char *
cstrncpy(char *dst, const char *src, size_t n)
/*@
    requires dst::BADS<> * src::WFS<l> & n > 0
    ensures res=dst;
*/
{
	if (n != 0) {
		char *d = dst;
		const char *s = src;

		do 
                  /*@
                     requires d::BADS<>*s::WFS<l> & n!=0
                     case{
                       n>=l -> ensures s::WFSeg<qq>*qq::char_star<0,s'>*s'::BADS<> * d::WFSeg<pp> * pp::char_star<0,pp2> * pp2::WFSem<d'> * d'::BADS<>;
                       n<l -> ensures n' = 0;
                     }
                  */
                {
			if ((*d++ = *s++) == 0) {
				/* NUL pad the remaining n-1 bytes */
				while (--n != 0)
                                  /*@
                                     requires d::BADS<> & n!=0
                                     ensures d::WFSem<d'>*d'::BADS<> & n'=0;
                                  */
					*d++ = 0;
				break;
			}
		} while (--n != 0);
	}
	return (dst);
}

int main() {
  int length = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  if (length < 1) {
      length = 1;
  }
  if (n < 1) {
      n = 1;
  }
  char* nondetArea = (char*) alloca(n * sizeof(char));
  char* nondetString = (char*) alloca(length * sizeof(char));
  nondetString[length-1] = '\0';
  cstrncpy(nondetArea, nondetString, n);
  return 0;
}
