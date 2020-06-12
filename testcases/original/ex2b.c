//Ex.3b: Use-After-Free
#include <stdio.h>
#include <stdlib.h>

#define N 10

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
