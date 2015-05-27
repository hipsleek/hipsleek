#include "stdlib.h"

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/* Origin: abbott@dima.unige.it
 * PR c/5120
 */

//#include <stdio.h>
//#include <stdlib.h>

typedef unsigned int FFelem;

FFelem FFmul(const FFelem x, const FFelem y)
//@ infer[@shape,@pre_n,@post_n] requires true ensures true;
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
//@ infer[@shape,@pre_n,@post_n] requires true ensures true;
{
  return f->deg;
}


void DUPFFshift_add(DUPFF f, const DUPFF g, int deg, const FFelem coeff)
//to add this spec for nobody
//@ requires true ensures true;
{
}


DUPFF DUPFFexgcd(DUPFF u)
//@ infer[@shape,@pre_n,@post_n] requires true ensures true;
{
  DUPFF  v, uf, ug, vf, vg;
  FFelem q, lcu, lcvrecip, p;
  int df, dg, du, dv;

  
    while ( DUPFFdeg(u) >= dv)
      //@ infer[@shape,@pre_n,@post_n] requires emp&true ensures emp&true;
    {
      du = DUPFFdeg(u);
      lcu = u->coeffs[du];
      q = FFmul(lcu, lcvrecip);
      DUPFFshift_add(u, v, du-dv, p-q);
      // dprint;
      DUPFFshift_add(uf, vf, du-dv, p-q);
      DUPFFshift_add(ug, vg, du-dv, p-q);
    }
  return u;
}
