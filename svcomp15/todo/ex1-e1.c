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
  FFelem *coeffs;
};

typedef struct DUPFFstruct *DUPFF;

//this func trigger diff type of error at line 38. see ex1-e2

void DUPFFexgcd_g( struct DUPFFstruct * f)
{
   f->coeffs[0] = 0;

  return;
}


/*
ERROR: at ex1-e1.c_24:3_24:20
Message: lhs is not an lvalue

RROR: at _0:0_0:0
Message: Can not find flow of DUPFFstruct

Context of Verification Failure: 1 File "",Line:0,Col:0

Last Proving Location: 1 File "ex1-e1.c",Line:24,Col:3

ERROR: at _0:0_0:0
Message: gather_type_info_var : unexpected exception Failure("Can not find flow of DUPFFstruct")


 */
//OK
/* void DUPFFexgcd_h(/\* struct DUPFFstruct *\/DUPFF f) */
/* { */
/*    f->coeffs[0] = 0; */

/*   return; */
/* } */



void DUPFFexgcd( const DUPFF f)
{
  FFelem i = f->coeffs[0];

  return;
}


