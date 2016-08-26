#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);

int main() {
  int i, j;
  int val;
  int length = __VERIFIER_nondet_int();
  if (length < 1 || length >= 2147483647 / sizeof(int)) length = 1;
  int *arr = alloca(length*sizeof(int));
  if (!arr) return 0;
  for (i=0; i<length; i++)
    /*@
      requires arr::arr_seg<i,length>
      ensures arr::arr_seg<i,length>;
     */
    {
    val = __VERIFIER_nondet_int();
    if (val < 0) {
      val = 0;
    }
    arr[i] = val;
  }
  for (j=0; j<length; j++)
    /*@
      requires arr::arr_seg<j,length>
      ensures arr::arr_seg<j,length>;
     */
    {
    while (arr[j] > 0)
      /*@
        requires x::arrI<_> & x=arr+j
        ensures x::arrI<_>;
      */
      {
      arr[j]--;
      }
  }
  return 0;
}
