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


//arith pointer
void test(){
  int * a = (int*)calloc(5,sizeof(int));
  a[0] = 1;
}

DUPFF DUPFFexgcd( const DUPFF f)
{
  DUPFF u;
  if (f->coeffs[0] == 0) return f;

  return u;
}

