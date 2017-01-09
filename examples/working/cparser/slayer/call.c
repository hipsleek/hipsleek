/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Unique ids over fun calls.
 **/

void f() {
  int x = 1;
  return;
}

void main() {
  int x = 0;
  f();
  //FAIL_IF(x!=0);
  //@ assert (x' = 0);
  return;
}
