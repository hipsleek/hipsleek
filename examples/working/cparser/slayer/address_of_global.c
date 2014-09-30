/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  y is an alias of the global x.
 **/

void** NULL = 0;

int x;

void main() {
  int *y = &x;
  *y = 0;
  //if(x!=0) *NULL = 0;
  //@ assert (x' = 0);
  return;
}
