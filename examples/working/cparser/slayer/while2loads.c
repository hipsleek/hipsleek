/*
  Copyright (c) Microsoft Corporation.  All rights reserved.

  A while loop whose test loads from two memory locations.

*/

//#include "slayer.h"

void* malloc(int size) __attribute__ ((noreturn))
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 -> requires true ensures res != null;
  }
*/;

void main()
{

  int *p;
  int *q;
  p = (int*) malloc(sizeof(int));
  q = (int*) malloc(sizeof(int));
  *p = 10;
  *q = 0;

  while (*p != *q)
    /*@
      requires p::int^<n>@L * q::int^<m> & m <= n
      ensures q::int^<n>;
    */
    (*q)++;

  //if (*p != *q) FAIL;
  //@ assert p'::int^<n> * q'::int^<m> & m = n;
}
