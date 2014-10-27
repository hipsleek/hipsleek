#include <stdlib.h>

#include "../../examples/working/cparser/stdhip.h"

int test_fun(int x, int y)
/*@
  infer [@shape,@term] requires true ensures true;
*/
{
  int* x_ref = (int*) malloc(sizeof(int));
  int* y_ref = (int*) malloc(sizeof(int));
  int* c = (int*) malloc(sizeof(int));
    *x_ref = x;
    *y_ref = y;
    *c = 0;
    while (*x_ref > *y_ref)
      //@    infer [@shape,@term] requires true ensures true;
      {
        *x_ref = *x_ref - 1;
        *c = *c + 1;
    }
    return *c;
}

/*
int main()
 {
  return test_fun(__VERIFIER_nondet_int(),__VERIFIER_nondet_int());
}
*/
