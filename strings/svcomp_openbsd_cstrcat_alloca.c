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

lemma_safe self::WFSeg<p> <- self::WFSeg<q>*q::WFSeg<p> .

lemma_safe self::WFS<> <-> self::WFSeg<q>*q::char_star<0,q2>*q2::BADS<> .

*/

extern int __VERIFIER_nondet_int(void);

char *cstrcat(char *s, const char *append)
  /*@
     requires s::WFS<>*append::WFS<>
     ensures res::WFSeg<p>*p::char_star<0,pp>*pp::BADS<>;
  */
{
	char *save = s;
	for (; *s; ++s)
          /*@
             requires s::WFS<>
             ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>;
          */
        ;
	while ((*s++ = *append++) != '\0')
          /*@
             requires s::char_star<_,q> * q::BADS<> * append::WFS<>   
             ensures append::WFSeg<qq>*qq::char_star<0,append'>*append'::BADS<> * s::WFSeg<q4>*q4::char_star<0,s'>*s'::BADS<>;
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
    int length3 = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    if (length2 < 2) {
        length2 = 2;
    }
    if (length3 < 1) {
        length3 = 1;
    }
    if (length2 - length3 < length1 || length3 > length2) return 0;
    char* nondetString1 = (char*) alloca(length1 * sizeof(char));
    char* nondetString2 = (char*) alloca(length2 * sizeof(char));
    nondetString1[length1-1] = '\0';
    nondetString2[length3-1] = '\0';
    cstrcat(nondetString2,nondetString1);
    return 0;
}
