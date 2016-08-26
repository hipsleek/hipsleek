#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

void test_fun(int a[], int N)
/*@
  requires a::arr_seg<0,N>
  ensures a::arr_seg<0,N>;
*/
{
    int i;
    int res;
    for (i = 0; i < N; i++)
      /*@
        requires a::arr_seg<i,N> & i>=0
        ensures a::arr_seg<i,N>;
      */
      {
        res = 1;
        
        
        if (a[i] == 0) {
            res = 1;
        }
        else
          if (a[i] < 0) {
            res = 0;
          }
        
        while (a[i] > 0)
          /*@
            requires x::arrI<_> & x=a+i & i>=0
            ensures x::arrI<_>;
          */
          {
            res = a[i];
            a[i]--;
        }
        
        a[i] = res;
        
    }
}

int main() {
  int array_size = __VERIFIER_nondet_int();
  if (array_size < 1 || array_size >= 2147483647 / sizeof(int)) {
     array_size = 1;
  }
  int* numbers = (int*) alloca(array_size * sizeof(int));
  test_fun(numbers, array_size);
}
