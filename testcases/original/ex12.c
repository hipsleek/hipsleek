//Ex.12
#include <stdlib.h>
int main() {
   int x, *a;
   int *p = malloc(sizeof(int));
   for (x = 10; x > 0; x--) {
       a = p;
       if (x == 1) {
           free(p);
       }
   }
   return 0;
}
