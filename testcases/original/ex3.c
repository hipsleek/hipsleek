//Ex.4: a possible double free
//      if the conditional statement is executed
#include <stdlib.h>
#include <stdint.h>

int main() {

   struct T {
       struct T* next;
   };

   struct T* x = NULL;
   struct T* y = NULL;

   y = malloc(sizeof(*y));
   intptr_t adressY = (intptr_t) y;

   free(y);

   x = malloc(sizeof(*x));
   intptr_t adressX = (intptr_t) x;

   if (adressX == adressY)
   { // if the second malloc returns the same value as the first, I should get here
       free(x);
   }

   free(x);

   return 0;
}
