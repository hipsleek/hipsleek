/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
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

lemma_safe self::WFS<> -> self::BADS<>.

lemma_safe self::WFS<> <-> self::WFSeg<q>*q::char_star<0,q2>*q2::BADS<>.

lemma_safe self::WFS<> <- self::WFSeg<q>*q::char_star<c,q2>*q2::WFS<> & c!=0.

*/

extern int __VERIFIER_nondet_int(void);


char *(cstrpbrk)(const char *s1, const char *s2)
  /*@
    requires s1::WFS<>*s2::WFS<>
    ensures true;
  */
 {
     const char *sc1;
     const char *s;
     int c;
     for (sc1 = s1; *sc1 != '\0'; sc1++) 
       /*@
          requires sc1::WFS<> * s2::WFS<>
          ensures sc1::WFSeg<sc1'>*sc1'::char_star<0,q>*q::BADS<>*s2'::WFSeg<qq>*qq::char_star<0,qqq>*qqq::BADS<> & flow __norm
               or sc1::WFSeg<sc1'>*sc1'::char_star<0,q>*q::BADS<>*s2'::WFSeg<qq>*qq::char_star<cc,qqq>*qqq::WFS<> & cc!=0 & flow __norm
               or eres::ret_char_star<p>*sc1::WFSeg<p>*p::char_star<cc,q>*q::WFS<> & flow ret_char_star;
       */
     {
         s = s2;
         c = *sc1;
         while (*s != '\0' && *s != (char)c)
           /*@
             requires s::WFS<>
             ensures s::WFSeg<s'>*s'::char_star<0,q>*q::BADS<>
                  or s::WFSeg<s'>*s'::char_star<c,q>*q::WFS<>; 
           */
         {    
           s++;
         }
         if (*s != c)
             return (char *)sc1;
     }
     return 0;                /* terminating nulls match */
 }

int main() {
    int length1 = __VERIFIER_nondet_int();
    int length2 = __VERIFIER_nondet_int();
    if (length1 < 1) {
        length1 = 1;
    }
    if (length2 < 1) {
        length2 = 1;
    }
    char* nondetString1 = (char*) alloca(length1 * sizeof(char));
    char* nondetString2 = (char*) alloca(length2 * sizeof(char));
    nondetString1[length1-1] = '\0';
    nondetString2[length2-1] = '\0';
    cstrpbrk(nondetString1,nondetString2);
    return 0;
}




/*=========================================================
#svcomp_cstrpbrk.c (fixed)
Why s = s2 but failed to prove s::WFS<> in the precondition?

Checking procedure while_38_5$int~char_star~char_star~char_star... 
Proving precondition in method while_47_9$int~char_star Failed.
  (may) cause: do_unmatched_rhs : s'::WFS<>@M(may)

Context of Verification Failure: svcomp_cstrpbrk_true_alloca.c_43:18_43:65

Last Proving Location: svcomp_cstrpbrk_true_alloca.c_47:9_55:10

Procedure while_38_5$int~char_star~char_star~char_star FAIL.(2)


Exception Failure("Proving precond failed") Occurred!
*/

