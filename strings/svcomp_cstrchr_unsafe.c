/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
 * not memory safe
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

*/

extern int __VERIFIER_nondet_int(void);

/* Returns some null-terminated string. */
char* __VERIFIER_nondet_String(void)
  /*@
     requires true
     ensures res::WFS<>;
  */ 
{
    int length = __VERIFIER_nondet_int();
    if (length < 1) {
        length = 1;
    }
    char* nondetString = (char*) malloc(length * sizeof(char));
    nondetString[length-1] = '\0';
    return nondetString;
}





char *(cstrchr)(const char *s, int c)
  /*@
     requires s::WFS<>
     ensures res::char_star<0,q>*q::BADS<>
     or res::char_star<c, q>*q::WFS<>;
  */
 {
     /* Scan s for the character.  When this loop is finished,
        s will either point to the end of the string or the
        character we were looking for.  */
     while (*s != '\0' && *s != (char)c)
       /*@
          requires s::WFS<>
          ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>
          or s::WFSeg<s'>*s'::char_star<c,q>*q::WFS<>; 
       */
         s++;
     return ( (*s == c) ? (char *) s : 0 );
 }

int main() {
    return *cstrchr(__VERIFIER_nondet_String(),__VERIFIER_nondet_int());
}


