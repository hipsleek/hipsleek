/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  We have a fun call convention to have unique actuals.
**/
int f(int a, int b)
/*@
  ensures res = a + b;
*/
{
  int y = a + b;
  return y;
}

void main() {
  int x = 0;
  int y = 1;

  int m = f(x,x); // Should become f(x1,x2)
  //@ assert (m' = 2*x');
  int n = f(x,y); // Should become f(x3,y1)
  //@ assert (n' = x' + y');
  return;
}
