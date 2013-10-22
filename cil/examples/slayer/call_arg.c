/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Access local/global through fun call.
 **/
//#include "slayer.h"

int g;

void f(int a, int *z)
/*@
  requires z::int^<a>
  ensures z::int^<g>;
*/
{
  int y = a;

  //FAIL_IF( y!=*z );
  //@ assert z'::int^<y>;
  *z = g;
  y = 13;
  return;
}

void main() {
  int x = 0;
  f(0, &x);
  //FAIL_IF( x!=g );
  //@ assert (x' = g');
  return;
}
