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

*/

extern int __VERIFIER_nondet_int(void);

int (cstrncmp)(const char *s1, const char *s2, int n)
  /*@
     requires s1::WFS<> * s2::WFS<>
     ensures true;
  */
 {
     unsigned char uc1, uc2;
     /* Nothing to compare?  Return zero.  */
     /* Loop, comparing bytes.  */
      while (n-->0) 
       /*@
          requires true
          ensures n'<0 & flow __norm
               or eres::ret_int<0> & n'=0 & flow ret_int;
       */
     {   
	if (n == 0){
           return 0;
        }
     }
     //uc1 = (*(unsigned char *) s1);
     //uc2 = (*(unsigned char *) s2);
     return ((uc1 < uc2) ? -1 : (uc1 > uc2));
 }

/*int main() {
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
    return cstrncmp(nondetString1,nondetString2,__VERIFIER_nondet_int());
}

*/
