/*  Copyright (c) Microsoft Corporation.  All rights reserved. */
//#include "slayer.h"

void free(int* p) __attribute__ ((noreturn))
/*@
  requires p::int*<_, stored_in_heap> & stored_in_heap
  ensures p = null;
*/;

void main() {
  int x;
  free(&x);
}
