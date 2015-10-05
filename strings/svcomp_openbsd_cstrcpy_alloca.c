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

char *cstrcpy(char *t, const char *from)
/*@
    requires t::BADS<> * from::WFS<>
    ensures res::WFSeg<q>*q::char_star<0,p>*p::BADS<>;
*/
{
	char *save = t;
	for (; (*t = *from) != '\0'; ++from, ++t)
          /*@
             requires t::BADS<> * from::WFS<>
             ensures from::WFSeg<from'>*from'::char_star<0,qq>*qq::BADS<> * t::WFSeg<t'>*t'::char_star<0,p>*p::BADS<>;
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
  
