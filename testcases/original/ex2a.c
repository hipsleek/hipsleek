//Ex.3a: Double Free after a loop
#include <stdio.h>
#include <stdlib.h>

#define N 10

int main() {
   int* array = (int*) malloc(sizeof(int) * N);
   for (int i = 0; i < N; i++) printf("%d\t", array[i]);
   free(array);
   // the double free problem won't be detected
   // unless use --unroll (N + 1) or more in SMACK
   free(array);
   return 0;
}
