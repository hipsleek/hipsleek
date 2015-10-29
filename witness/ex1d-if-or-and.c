
// ../hip ex1d-if-or-and.c --witness-gen "main:1"
//../hip ex1d-if-or-and.c --witness-gen "main:2,1,1"

extern void __VERIFIER_error();
extern int __VERIFIER_nondet_int();


int main(void) {
  int n = 3;
  int m = __VERIFIER_nondet_int();
  if (m<n || n>2 && n<=4) {
  ERROR: __VERIFIER_error();
  }
  return 0;
}
