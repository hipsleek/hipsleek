//#include <stdlib.h>

//extern int __VERIFIER_nondet_int(void);

// ../hip ex1a-alloca-while.c -infer "@shape_prepost@term"

void loop (int* x, int* y)
/*
  infer[@shape_prepost]
  requires true
  ensures true;
*/
{
  while (*x > 0) {
    while (*y > 0) {
      *y = *y - 1;
    }
    *x = *x - 1;
  }
}

int main() 
{
  return 0;
}
