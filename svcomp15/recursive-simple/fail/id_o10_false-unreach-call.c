// extern int __VERIFIER_nondet_int();
// extern void __VERIFIER_error();

int __nondet_int()
/*@
  requires true
  ensures true;
*/;

void __error()
/*@
  requires emp & true
  ensures emp & true & flow __Error;
*/;

int id(int x)
/*@
  case {
  x>=0 -> ensures emp & res=x;
  x<0 -> requires Loop ensures false;
  }
 */
{
  if (x==0) return 0;
  return id(x-1) + 1;
}

void main()
/*@
  requires true
  ensures true;
*/
{
  int input = __nondet_int();
  int result = id(input);
  if (result == 10) {
    __error();
  }
}
