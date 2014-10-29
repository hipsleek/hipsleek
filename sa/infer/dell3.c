#include "stdhip.h"

void main()
/*@
  infer[@shape]
  requires true
  ensures true;
*/
{
  int* x = alloca(sizeof(int));
  int* y = alloca(sizeof(int));
  while (*y < *x) 
  /*@
    infer[@shape]
    requires true
    ensures true;
  */
  {
    *x = *x - 1;
  }
}
