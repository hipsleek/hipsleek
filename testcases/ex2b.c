// Ex2b: Use after free
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
   //if the following line is used, use --unroll (N+1) or more
  // for (int i = 0; i < N; i++) printf("%d\t", array[i]);
   free(array);

   // the following line alone won't triger use-after-free alarm,
   // in SMACK as it will be eliminated by compiler's optimisation
   // it would be interesting to check the bpl & ll files
   int i = array[1];
   // uncomment the following line will triger the use-after-free alarm
   // as the dereference of array after free cann't be ignored
   // printf("%d", i);
   return 0;
}
