void __error()
/*@
  requires emp & true
  ensures emp & true & flow __Error;
*/;

void f(int n)
/*@
  case {
  n<3 -> ensures emp & true;
  n>=3 -> ensures emp & true & flow __Error;
  }
 */
{
  if (n<3) return;
  n--;
  f2(n);
  __error();
}

void f2(int n)
/*@
  case {
  n<3 -> ensures emp & true;
  n>=3 -> ensures emp & true & flow __Error;
  }
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
  f(4);
}
