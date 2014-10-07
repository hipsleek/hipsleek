/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  fe drops some casts?
**/
void main() {
  int x;
  (int*)x = &x;
  return;
}
