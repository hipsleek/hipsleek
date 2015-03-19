#include "stdlib.h"

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/* Origin: abbott@dima.unige.it
 * PR c/5120
 */

//#include <stdio.h>
//#include <stdlib.h>

typedef unsigned int FFelem;

/* FFelem FFmul(const FFelem x, const FFelem y) */
/* { */
/*   return x; */
/* } */


struct DUPFFstruct
{
  int maxdeg;
  int deg;
  FFelem *coeffs;
};

typedef struct DUPFFstruct *DUPFF;


/* int DUPFFdeg(const DUPFF f) */
/*   //@ infer [@shape,@post_n] requires true ensures true; */
/* { */
/*   return f->deg; */
/* } */


DUPFF DUPFFnew(const int maxdeg)
  //@ infer [@shape,@pre_n,@post_n] requires true ensures true;
{
  DUPFF ans = (DUPFF)malloc(sizeof(struct DUPFFstruct));
  ans->coeffs = 0;
  if (maxdeg >= 0) ans->coeffs = (FFelem*)calloc(maxdeg+1,sizeof(FFelem));
  ans->maxdeg = maxdeg;
  ans->deg = -1;
  return ans;
}



int main()
   //@ infer [@shape,@post_n] requires emp & true ensures emp & true;
{
  DUPFF f, g, cf, cg, h;
  f = DUPFFnew(1);
  // dprint;
  f->coeffs[1] = 1; f->deg = 1;
  g = DUPFFnew(2); g->coeffs[2] = 1; g->deg = 2;

  /* h = DUPFFexgcd(&cf, &cg, f, g); */
  /* h = h; */
  return 0;
}
