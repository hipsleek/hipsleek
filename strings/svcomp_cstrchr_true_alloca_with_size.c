/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
 */
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

*/

extern int __VERIFIER_nondet_int(void);

char *(cstrchr)(const char *s, int c)
 /*@
     requires s::WFS<m>
     ensures res::char_star<c, q>*q::WFS<n>
     or res::char_star<0,_>;
  */
 {
     /* Scan s for the character.  When this loop is finished,
        s will either point to the end of the string or the
        character we were looking for.  */
     while (*s != '\0' && *s != (char)c)
       /*@
          requires s::WFS<m>
          ensures s::WFSeg<s',m>*s'::char_star<0,q>*q::BADS<>
          or s::WFSeg<s',n>*s'::char_star<c,q>*q::WFS<m-n-1>; 
       */
         s++;
     return ( (*s == c) ? (char *) s : 0 );
 }

int main()
/*@
   requires true 
   ensures res = 0;
*/ 
{
    int length = __VERIFIER_nondet_int();
    if (length < 1) {
        length = 1;
    }
    char* nondetString = (char*) alloca(length * sizeof(char));
    nondetString[length-1] = '\0';
    cstrchr(nondetString,__VERIFIER_nondet_int());
    return 0;
}


