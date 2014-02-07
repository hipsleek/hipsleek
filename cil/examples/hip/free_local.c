/*  Copyright (c) Microsoft Corporation.  All rights reserved. */
//#include "slayer.h"

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

void free(int* p) __attribute__ ((noreturn))
/*@
  requires p::int*<tttt, heap> & heap
  ensures p = null;
*/;

void main() {
  int x;
  int *ppp = malloc(1);
  //ppp = 1;
  *ppp = 10;
  //@ assert ppp'::int^<10, _>;
  ///@ dprint;
  int* zzzz = &x;
  ///@ dprint;
  //*ppp = 10;
  ///@ dprint;
  
  //free(zzzz);
  free(ppp);
  //@ assert (ppp = null);
  ///@ dprint;
}
