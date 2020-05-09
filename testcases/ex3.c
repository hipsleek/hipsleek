//Ex.3: a possible double free
//      if the conditional statement is executed

struct T {
    struct T* next;
};

typedef long int intptr_t;

struct T* malloc(int size)
/*@
  case {
    size <= 0 -> requires true ensures res = null;
    size > 0 -> requires true ensures res::T<_>;
  }
*/;

int main() {
   struct T* x = NULL;
   struct T* y = NULL;

   y = malloc(sizeof(*y));
  //  intptr_t adressY = (intptr_t) y;
   struct T* adressY = y;

   free(y);

   x = malloc(sizeof(*x));
  //  intptr_t adressX = (intptr_t) x;
   struct T* adressX = x;

   if (adressX == adressY)
   { // if the second malloc returns the same value as the first, I should get here
       free(x);
   }

   free(x);

   return 0;
}
