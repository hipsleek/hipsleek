/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Assign to a local, but by passing it's address down a chain of function
  calls. Test for PS #146.
**/
//#include "slayer.h"

int a,b,c;

void h(int** i)
{
  **i = &a;
}

void g(int** i)
{
  h(i);
}

void f(int* i)
{
  int** pi;
  pi = &i;
  g(pi);
}

void main ()
{
  int *p = (int*) malloc (sizeof(int));
  *p = &b;
  f(p);
  *p = &c;
  f(p);
  *p = 0;
  f(p);

  // assert *p != 0
  //FAIL_IF( (*p) == 0 );
  //@ assert p'::int^<n> & n != 0;
  return;
}
