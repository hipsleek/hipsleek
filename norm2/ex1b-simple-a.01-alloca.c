//#include <stdlib.h>

//extern int __VERIFIER_nondet_int(void);

void foo(int* x)
/*@
  infer[@shape_prepost,@classic,@term]
  requires true
  ensures true;
*/
{
  //dprint;
  *x = 0;
}

int main() {
  return 0;
}
