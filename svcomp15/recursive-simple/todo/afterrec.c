void __VERIFIER_error1()
/*@
  requires true
  ensures true & flow __Error;
*/;

void f(int n)
/*@
  requires true
  ensures n<3 & flow __norm or n>=3 & flow __Error;
*/
{
  if (n<3) return;
  n--;
  f(n);
  __VERIFIER_error1();
}

/* void main() { */
/*   f(2); */
/* } */
