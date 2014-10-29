#include "stdhip.h"

void main()
/*@
  infer[@shape,@post_n,@term]
  requires true
  ensures true;
*/
{
  int* x = alloca(sizeof(int));
  int* y = alloca(sizeof(int));
  while (*y < *x) 
  /*@
    infer[@shape,@post_n,@term]
    requires true
    ensures true;
  */
  {
    *x = *x - 1;
  }
}
