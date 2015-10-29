
// ../hip ex1b-if-complex.c --witness-gen "main:1,1"


extern void __VERIFIER_error();
extern int __VERIFIER_nondet_int();


int main(void) {
  int n = 3;
  int m = __VERIFIER_nondet_int();
  if ( n>2 && m<1 || m>n) {
  ERROR: __VERIFIER_error();
  }
  return 0;
}
