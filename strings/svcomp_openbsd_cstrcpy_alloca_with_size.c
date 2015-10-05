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

char *cstrcpy(char *t, const char *from)
/*@
    requires t::BADS<> * from::WFS<n2>
    ensures res::WFSeg<q,n1>*q::char_star<0,p>*p::BADS<>;
*/
{
	char *save = t;
	for (; (*t = *from) != '\0'; ++from, ++t)
          /*@
             requires t::BADS<> * from::WFS<n2>
             ensures from::WFSeg<from',n2>*from'::char_star<0,qq>*qq::BADS<> * t::WFSeg<t',n1>*t'::char_star<0,p>*p::BADS<>;
          */
        ;

	return(save);
}

int main() 
/*@
   requires true
   ensures res=0;
*/  
{
  int length1 = __VERIFIER_nondet_int();
  int length2 = __VERIFIER_nondet_int();
  if (length1 < 1) {
      length1 = 1;
  }
  if (length2 < 1) {
      length2 = 1;
  }
  if (length1 < length2) return 0;
  char* nondetArea = (char*) alloca(length1 * sizeof(char));
  char* nondetString = (char*) alloca(length2 * sizeof(char));
  nondetString[length2-1] = '\0';
  cstrcpy(nondetArea,nondetString);
  return 0;
}
  

/*======================================
#svcomp_openbsd_cstrcpy.c
why we can't use 'to' in specs?

==========================================*/
