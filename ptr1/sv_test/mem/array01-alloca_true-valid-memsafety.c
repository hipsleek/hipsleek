#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int test_fun(int a[], int N)
/*@
  requires a::arr_seg<0,N>
  ensures a::arr_seg<0,N>;
 */
{
    int i;
    int res = 0;
    for (i = 0; i < N; i++)
      /*@
        requires a::arr_seg<i,N>
        ensures a::arr_seg<i,N>;
       */
      {
        while (a[i] > 0)
          /*@
            requires x::arrI<_> & x=a+i
            ensures x::arrI<_>;
           */
        {
            a[i]--;
            res++;
        }
    }
    return res;
}


int main() {
  int array_size = __VERIFIER_nondet_int();
  if (array_size < 1 || array_size >= 2147483647 / sizeof(int)) {
     array_size = 1;
  }
  int* numbers = (int*) alloca(array_size * sizeof(int));
  test_fun(numbers, array_size);
}

