#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

void foo(int* x)
{
  //@dprint;
  *x = 0;
}

int test_fun(int x, int y)
{
    int* x_ref = alloca(sizeof(int));
    int* y_ref = alloca(sizeof(int));
    int* c = alloca(sizeof(int));
    *x_ref = x;
    *y_ref = y;
    //@dprint;
    foo(x_ref);
    *c = 0;
    return 1;
}

int main() {
  return test_fun(__VERIFIER_nondet_int(),__VERIFIER_nondet_int());
}
