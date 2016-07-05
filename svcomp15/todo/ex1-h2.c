#include "stdlib.h"

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/* Origin: abbott@dima.unige.it
 * PR c/5120
 */

//#include <stdio.h>
//#include <stdlib.h>

typedef unsigned int FFelem;


struct DUPFFstruct
{
  int maxdeg;
  int deg;
  FFelem *coeffs;
};

typedef struct DUPFFstruct *DUPFF;



DUPFF DUPFFnew(const int maxdeg)
  //@ infer [@shape,@pre_n,@post_n] requires true ensures true;
/* infer [@shape,@pre_n,@post_n]
  case {
    maxdeg>=0 -> requires true ensures true;
    maxdeg<0 -> requires true ensures true;
}
*/
{
  DUPFF ans = (DUPFF)malloc(sizeof(struct DUPFFstruct));
  ans->coeffs = 0;
  if (maxdeg >= 0) ans->coeffs = (FFelem*)calloc(maxdeg+1,sizeof(FFelem));
  ans->maxdeg = maxdeg;
  ans->deg = -1;
  return ans;
}


/*
*********************************************************
SHAPE
*********************************************************
[ GP_25(res_2136) ::=
 res_2136::DUPFFstruct_star<deref_f_r_2055,o_2141> *
 deref_f_r_2055::DUPFFstruct<maxdeg_2137,v_int_44_2138,v_int_star_42_2110>&
 v_int_star_42_2110=null
 or res_2136::DUPFFstruct_star<deref_f_r_2055,o_2141> *
    v_int_star_42_2110::int_star<Anon_2139,o_2140> *
    deref_f_r_2055::DUPFFstruct<maxdeg_2137,v_int_44_2138,v_int_star_42_2110>
 (4,5)]
*************************************


!!!  post_2174(maxdeg,flow) = ( (maxdeg+1)<=0) \/ ( 0<=maxdeg)
!!! n_base:3
!!! bottom_up_fp:[( post_2174(maxdeg,flow), ((maxdeg+1)<=0 | 0<=maxdeg))]
!!! fixpoint:[( post_2174(maxdeg,flow), ((maxdeg+1)<=0 | 0<=maxdeg), true, true)]
!!! REL POST :  post_2174(maxdeg,flow)
!!! POST:  ((maxdeg+1)<=0 | 0<=maxdeg)
!!! REL PRE :  true
!!! PRE :  true


 */
