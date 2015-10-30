#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

void loop (int* x)
/*@
  infer[@shape_prepost]
  requires true
  ensures true;
*/
{
  if (*x <= 0) return;
  else {
    *x = *x - 1;
    loop(x);
  }
}

int main() 
{
  return 0;
}
