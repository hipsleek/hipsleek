/*
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Update global var in various ways.
  A testcase for PS#211, where x=nondet() was being translated as Mov(x,*),
  rather than Store(x,*).
  This program should be SAFE.
*/
//#include <slayer.h>

int x ;

int f(int x)
/*@
  ensures res = x;
*/
{
  return x;
}


int f_cantinline_me(int x)
/*@
  ensures res = x;
*/
{
  int i, y = 0;
  for (y=0; y<5; y++) { i++; }
  return x;

}

void main() {
  int y ;

  x = 0;
  //if (x != 0) FAIL;
  //@ assert (x' = 0);

  x = f(0);
  //if (x != 0) FAIL;
  //@ assert (x' = 0);

  x = f_cantinline_me(0);
  //if (x != 0) FAIL;
  //@ assert (x' = 0);

  //x = nondet();
  y = x ;
  //if (x != y) FAIL;
  //@ assert (x' = y');

  return;
}
