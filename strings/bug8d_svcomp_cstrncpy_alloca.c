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

WFSem<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSem<p> & v=0
  inv true;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;

//lemma_safe self::WFS<> -> self::BADS<>.

//lemma_unsafe self::WFSeg<q>*q::BADS<> <- self::BADS<>.
*/

extern int __VERIFIER_nondet_int(void);

void while1(char *s, int n)
  /*@
	requires s::BADS<>&n>0
        ensures true;
  */
{
  while (n-- != 0)
    /*
       requires s::BADS<> & n>=0
       ensures s::WFSeg<s'>*s'::BADS<> & n' = -1;
    */
    /*@
        requires s::BADS<>
        case {
          n >= 0 -> ensures s::WFSem<s'>*s'::BADS<> & n'=-1;
          n < 0 -> ensures false;
        }
     */
  {
     *s++ = '\0';
  }
 }

