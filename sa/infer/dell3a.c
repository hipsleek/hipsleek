#include "stdhip.h"

void main()
{
  int* x = alloca(sizeof(int));
  int* y = alloca(sizeof(int));
  while (*y < *x) 
  {
    *x = *x - 1;
  }
}
