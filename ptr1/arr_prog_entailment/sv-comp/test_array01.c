#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int test_fun(int a[], int N)
/*@
  requires a::Aseg<0, N>
  ensures a::Aseg<0, N>;
 */
{
    int i;
    int res = 0;
    for (i = 0; i < N; i++)
      /*@
	requires a::Aseg<i, N> & i>=0 & i<=N
	ensures a::Aseg<i, N>;
      */
      {
        while (a[i] > 0)
	  /*@
	    requires a::Elem<i, _>
	    ensures a::Elem<i, _>;
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
