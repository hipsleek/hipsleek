
// ../hip ex1-aftercall-false.c --witness-gen "main:;f:2;f:1"
extern void __VERIFIER_error();

void f(int n) {
  if (n<3) return;
  n--;
  f(n);
  ERROR: __VERIFIER_error();
}

int main(void) {
  f(4);
}
