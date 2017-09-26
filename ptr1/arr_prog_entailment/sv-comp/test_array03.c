#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

void test_fun(int a[], int N)
/*@
  requires a::Aseg<0, N>
  ensures a::Aseg<0, N>;
*/
{
    int i;
    int res1;
    for (i = 0; i < N; i++)
      /*@
	requires a::Aseg<i, N> & i>=0 & i<=N
	ensures a::Aseg<i, N>;
      */
      {
        res1 = 1;
        if (a[i] == 0) {
            res1 = 1;
        } else if (a[i] < 0) {
            res1 = 0;
        }
        while (a[i] > 0)
	  /*@
	    requires a::Elem<i, _>
	    ensures a::Elem<i, _>;
	  */
	  {
            res1 = res1 * a[i];
            a[i]--;
        }
        a[i] = res1;
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
