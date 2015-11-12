#include <stdlib.h>

/*@

WFS<> ==
  self::char_star<0,q>*q::BADS<> 
  or self::char_star<v,q>*q::WFS<> & v!=0 
  inv true;

WFSeg<p, n> ==
  self=p & n=0
  or self::char_star<v,q>*q::WFSeg<p, n-1> & v!=0
  inv n>=0;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;

lemma_safe self::WFSeg<p,n1+n2> <- self::WFSeg<q,n1>*q::WFSeg<p,n2>.

lemma_safe self::WFS<> <-> self::WFSeg<q,n>*q::char_star<0,q2>*q2::BADS<> .

*/

extern int __VERIFIER_nondet_int(void);

char* loop (char* s)
{
  char *s1 = s;
  /* Move s so that it points to the end of s1.  */
  while (*s != '\0')
    s++;
  return s1;
}

int main()
{
    int length = __VERIFIER_nondet_int();
    if (length < 1) {
        length = 1;
    }
    char* nondetString = (char*) alloca(length * sizeof(char));
    //@ dprint;
    nondetString[length-1] = '\0';
    //@ dprint;
    //loop(nondetString);
    return 0;
}
