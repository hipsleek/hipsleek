#include <stdlib.h>
/*@
WFSeg<p, n> ==
  self=p & n=0
  or self::char_star<v,q>*q::WFSeg<p, n-1> & v!=0
  inv n>=0;
*/

extern int __VERIFIER_nondet_int(void);
int main()
{
    int length = __VERIFIER_nondet_int();
    if (length < 1) {
        length = 1;
    }
    char* nondetString = (char*) alloca(length * sizeof(char));
    char* nondetString2 = (char*) alloca(length * sizeof(char));
    /* nondetString[length-1] = '\a'; */
    nondetString2[length-1] = '\0';
    *nondetString++ = '\a';
    *nondetString = '\0';
    *++nondetString2 = '\a';
    return 0;
}

/*
tmp___0 = (116, ):alloca((int)length * 1)
nondetString = (119, ):__cast_void_pointer_to_char_star__(tmp___0)
(120, ):__finalize_string(nondetString, (int)length - 1) // TO FIX
tmp___1 = nondetString
nondetString = (124, ):__plus_plus_char(nondetString)
(125, ):__write_char(tmp___1, 7)
(126, ):__write_char(nondetString, 0) // TO FIX
(127, ):return 0}}

*/
