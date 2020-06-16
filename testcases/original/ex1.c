//Ex.1: array inside struct
#include <stdio.h>
#include <stdlib.h>

struct overflow{
   int a[9];
   double c;
};

int main() {
   struct overflow* s = (struct overflow*)malloc(sizeof(struct overflow));

   int i = 10;
   s->a[i] = 0; //buffer-overflow 1
   s->a[i+1] = 0; //buffer-overflow 2
   s->c = 2.0;

   free(s);
   return 0;
}
