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


int DUPFFdeg(const DUPFF f)
{
  return f->deg;
}



DUPFF DUPFFexgcd(DUPFF *fcofac, DUPFF *gcofac, const DUPFF f, const DUPFF g)
{
  DUPFF u, v, uf, ug, vf, vg;
  /* FFelem q, lcu, lcvrecip, p; */
  int df, dg, du, dv;

  df = DUPFFdeg(f);
  dg = DUPFFdeg(g);
  if (df < dg)
    return 1;
      // DUPFFexgcd(gcofac, fcofac, g, f);

  return u;
}
