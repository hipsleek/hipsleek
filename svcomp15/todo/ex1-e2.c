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

/*
ERROR: at ex1-e2.c_24:9_24:11
Message: OpAssign : lhs and rhs do not match 2
 */
void DUPFFexgcd( const DUPFF f)
{
  FFelem i = f->coeffs[0];

  return;
}

/* void foo( const DUPFF f) */
/* { */
/*   FFelem i = f->coeffs[0]; */

/*   return; */
/* } */
