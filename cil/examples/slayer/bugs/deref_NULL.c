/*
  Copyright (c) Microsoft Corporation.  All rights reserved.
*/
void** NULL = 0;

void main() {
  *NULL = (void*)1; // there's a bug in this assignment
  return;
}
