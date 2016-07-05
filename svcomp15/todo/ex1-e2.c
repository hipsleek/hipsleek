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
  // int *coeffs;// OK
};

typedef struct DUPFFstruct *DUPFF;

/*
ERROR: at ex1-e2.c_24:9_24:11
Message: OpAssign : lhs and rhs do not match 2


=======================
!!!>>>>>> mismatch ptr coeffs_27_1844::int_star<val_1853,offset_1854> is not found (or inst) in the lhs <<<<<<
!!!>>>>>> mismatch ptr coeffs_27_1844::int_star<val_1855,offset_1856> is not found (or inst) in the lhs <<<<<<

-GOT
data DUPFFstruct {
  int coeffsVAL_12;
}
-EXPECTED
data DUPFFstruct {
  int_star coeffsVAL_12;
}
 */
void DUPFFexgcd( const DUPFF f)
{
  FFelem i = f->coeffs[0];

  return;
}

/* void foo(int* i) */
/* { */
/*   // i[0] = 0; */
/*   int j = i[0]; */

/*   return; */
/* } */
