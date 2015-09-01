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


int (cstrncmp)(const char *s1, const char *s2)
  /*@
     requires s1::WFS<> * s2::WFS<>
     ensures res=0;
  */
 {
     while (*s1 == *s2) 
       /*@
          requires s1::WFS<> * s2::BADS<>
          ensures s1::WFSeg<q>*q::char_star<c,s1'>*s1'::WFS<>*s2::WFSeg<qq>*qq::char_star<c,s2'>*s2'::BADS<> & c != 0;
       */
     {
         if (*s1 == '\0')
           {
             return 0;
           }
         s1++;
         s2++;
     }
     return 0;
 }


/*================================
#bug7.c
Post condition cannot be derived:
(may) cause: [OrL[
  (must) cause: 1.2c: ante flow:ret_int#E conseq flow: __norm#E are incompatible flow types,
  (must) cause: do_unmatched_rhs : s2::WFSeg<qq_2777>@M(must)
],valid]
*/
