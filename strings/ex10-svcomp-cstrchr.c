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
      while (*s != '\0' && *s != (char)c)
        /*@
          requires s::WFS<>
          ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>
          or s::WFSeg<s'>*s'::char_star<c,q>*q::WFS<>; 
       */
        s++;
     return ( (*s == c) ? (char *) s : 0 );
 }

int main() 
{
    return *cstrchr(__VERIFIER_nondet_String(),__VERIFIER_nondet_int());
}

/*
# ex10.c (FIXED)

We cannot cast into char_pointer at the moment?

ERROR: at _0:0_0:0
Message: Can not find flow of char_star

Last Proving Location: void_pointer_casting_proc_1:0_6:3

ERROR: at _0:0_0:0
Message: Can not find flow of int_star

Last Proving Location: void_pointer_casting_proc_1:0_6:3

ERROR: at void_pointer_casting_proc_5:25_5:40
Message: UNIFICATION ERROR : at location {(Line:5,Col:25),(Line:5,Col:40)} types char_star and int_star are inconsistent


*/
