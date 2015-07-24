void __error()
/*@
  requires emp & true
  ensures emp & true & flow __Error;
*/;


/*@
relation P1(int x).
relation Q1(int x).
 */

void f(int n)
/*
  case {
  n<3 -> ensures emp & true;
  n>=3 -> ensures emp & true & flow __Error;
  }
 */
/*@
infer [P1,Q1]
  requires P1(n) ensures Q1(n);
 */
{
  if (n<3) return;
  n--;
  f(n);
  __error();
}

void main()
/*@
  requires true
  ensures true;
*/
{
  f(2);
}
