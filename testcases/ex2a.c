// Ex2a: Double free
#define N 10
/*@
pred arr_seg<p,n> == self=p & n=0
  or self::int_star<_>*q::arr_seg<p,n-1> & q = self + 1 & n > 0
  inv n>=0.
*/

int* malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size >  0 ->
      requires true
      ensures res::int_star<_>;
  }
*/;

int main() {
   int* array = (int*) malloc(sizeof(int) * N);
//    for (int i = 0; i < N; i++) {
//        //printf("%d\t", array[i]);
//        array[i] = array[i];
//    }
  free(array);
  // the double free problem won't be detected
  // unless use --unroll (N + 1) or more in SMACK
  free(array);
  return 0;
}
