#define N 10
/*@
pred arr_seg<p,n> == self=p & n=0
  or self::int_star<_>*q::arr_seg<p,n-1> & q = self + 1 & n > 0
  inv n>=0.
*/

/*
HIP manages to detect the error if malloc's spec returns an int_star. If malloc's spec returns an arr_seg, the first free will result in a false heap and pure, and the verification will
mistakenly succeed.

Proving precondition in method free$int_star Failed.
  (must) cause: do_unmatched_rhs : array'::int_star<Anon_1934>@M(must)

Context of Verification Failure: _0:0_0:0

Last Proving Location: double-free.c_44:2_44:13

Procedure main$ FAIL.(2)


Exception Failure("Proving precond failed") Occurred!
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
