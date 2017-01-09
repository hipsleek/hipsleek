/*  Copyright (c) Microsoft Corporation.  All rights reserved. */
//#include "slayer.h"

/*@
pred_prim memLoc<heap:bool,size:int>
  inv size>0;
*/

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res::memLoc<h,s> & h;
  }
*/;

void free(int* p) __attribute__ ((noreturn))
/*@
  requires p::int*<_>
  ensures p = null;
*/;

void main() {
  int x;
  free(&x);
}
