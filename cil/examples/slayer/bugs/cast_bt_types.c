/*
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Expected result: UNSAFE.
*/

//#include "slayer.h"

struct I { int i; };
struct IJ { int i; int j; };

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

void main()
{
  int *x;
  struct I *pi;
  struct IJ *pij;

  x = malloc(sizeof(int));
  // x->(int) []

  pi = (struct I*)x;
  pi->i = 32;
  // x->(I) [i:32]

  pij = (struct IJ*)x;
  pij->i = 10;
  pij->j = 100; // UNSAFE!
  // x->(IJ) [i:10;j:100]

  x = (int*)pij;
  free(x);

}
