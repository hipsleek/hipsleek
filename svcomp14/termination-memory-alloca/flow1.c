#include <stdlib.h>

//extern int __VERIFIER_nondet_int(void);

int test_fun(int x)
 /*@ requires x>=0 ensures true;
       */
{
  int* x_ref = alloca(sizeof(int));
  *x_ref = x;
  while (*x_ref > 0)
    /* requires x>=0 ensures x'=0;
     */
    {
      /* if(0) { */
      /*   // replace assume */
      /*   return 0; */
      /* } */
      *x_ref = *x_ref-1;
    }
  return *x_ref;
}
