#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
 /*@ requires x>=0 ensures true;
       */
{
  int* x_ref = alloca(sizeof(int));
  int* y_ref = alloca(sizeof(int));

  *x_ref = x;
  *y_ref = y;

  while (*x_ref > 0)
    /* requires x>=0 ensures x'=0; */
    {
      if(*y_ref >= 0) {
        // replace assume
        return 0;
      }
      *x_ref = *x_ref-1;
      //x = x-1;
    }
  return *x_ref;
}
