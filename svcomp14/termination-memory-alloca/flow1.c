#include <stdlib.h>

//extern int __VERIFIER_nondet_int(void);

int test_fun(int x)
 /*@ requires x>=0 ensures true;
       */
{
    while (x > 0)
      /*@ requires x>=0 ensures x'=0 & res=0;
       */
      {
       /*  if(x=0) { */
      /*     // replace assume */
      /*     return 0; */
      /* } */
      x = x-1;
    }
    return x;
}
