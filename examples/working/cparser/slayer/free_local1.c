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
    size >  0 -> requires true ensures res::memLoc<h,s> & h & res != null;
  }
*/;

void free(int* p) __attribute__ ((noreturn))
/*@
  requires p::int*<_> * p::memLoc<h,_> & h
  ensures p = null;
*/;

void main() {
  int x;
  int* p  = malloc(1);
  *p = 1;
  ////@ assert p'::int^<1>;
  free(p);
}
