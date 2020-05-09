/* Contributed by Kamil Dudka. */
//Ex.6: tricky memory leak

#include <stdlib.h>
#include <string.h>

char a[sizeof(int*)];

void foo(void)
{
  int *p = (int *)malloc(10); // This p will leak
  memcpy(a, &p, sizeof p);
}

int main(void)
{
  foo();
  void *p ; // this p will free
  memcpy(&p, a, sizeof p);
  free(p);
}
