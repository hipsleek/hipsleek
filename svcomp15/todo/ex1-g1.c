#include "stdlib.h"

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/* Origin: abbott@dima.unige.it
 * PR c/5120
 */

//#include <stdio.h>
//#include <stdlib.h>

typedef unsigned int FFelem;

FFelem FFmul(const FFelem x, const FFelem y)
{
  return x;
}


struct DUPFFstruct
{
  int maxdeg;
  int deg;
  FFelem *coeffs;
};

typedef struct DUPFFstruct *DUPFF;

//  ../../hip ex1-g.c -infer "@shape,@post_n" 
int DUPFFdeg(const DUPFF f)
// infer[@shape,@post_n] requires emp&true ensures emp&true;
{
  return f->deg;
}

/*
EBase exists (Expl)[](Impl)[maxdeg_32_2475; deg_32_2476; 
       offset_32_2482](ex)[]value_32_2483::DUPFFstruct<maxdeg_32_2475,deg_32_2476,DP_DP_HP_2478> * 
       f::DUPFFstruct_star<value_32_2483,offset_32_2482>&MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists offset_32_2515: f::DUPFFstruct_star<value_32_2468,offset_32_2515> * 
           value_32_2468::DUPFFstruct<maxdeg_32_2475,deg_32_2476,DP_DP_HP_2478>&
           deg_32_2476=res & offset_32_2515=offset_32_2482&
           {FLOW,(4,5)=__norm#E}[]
 */
