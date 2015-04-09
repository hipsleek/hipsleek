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
  x>=0 & x<=3 -> ensures emp & res=x;
  x>3 -> ensures emp & res=3;
  x<0 -> requires Loop ensures false;
  }
 */
{
  if (x==0) return 0;
  int ret = id(x-1) + 1;
  if (ret > 3) return 3;
  return ret;
}

void main()
/*@
  requires true
  ensures true;
*/
{
  int input = __nondet_int();
  int result = id(input);
  if (result == 2) {
    __error();
  }
}
