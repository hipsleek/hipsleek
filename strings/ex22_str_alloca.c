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
/*| "char" -> typ_name ^ " " ^ proc_name ^ " (void_star p)\n" ^*/
/*                      "  case { \n" ^*/
/*                      "    p =  null -> ensures res = null; \n" ^*/
/*                      "    p != null -> requires p::memLoc<h,s> & h\n" ^ */
/*                      "                 ensures res!=null; \n" ^*/
/*                      "  }\n"*/


    nondetString[length-1] = '\0';
/*    let proc_str = typ1_name ^ " " ^ pname ^ " (" ^ typ1_name ^ " x, " ^ typ2_name ^ " n)\n"*/
/*                          ^ "requires x::WFSeg<p,m> & n < m \n"*/
/*                          ^ "ensures x::WFSeg<q,n>*q::char_star<0,r>*r::WFSeg<p,m-n-1> ;\n"*/
    return 0;
}
