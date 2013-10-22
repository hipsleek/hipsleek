/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  The frontend (ast) used to treat a struct as a scalar.
 **/

struct s {
  int *a;
  int *b;
};

void main() {
  struct s x;
  int **ptr;
  int y;

  x.b = &y;
  ptr = &x.a;
  ptr++;       // fe translates this to ptr = ptr !
  *ptr = 0;
  *x.b = 0;    // should signal a memory unsafety here
}
