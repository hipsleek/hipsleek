//Ex10 : Invalid free in stack
#include <stdlib.h>

int main(void) {
 int x = 1;
 int *y = &x;
 free(y);
 return 0;
}
