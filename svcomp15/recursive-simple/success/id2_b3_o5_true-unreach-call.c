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

/*@
relation P1(int x).
relation Q1(int x, int y).
 */

int id(int x)
/*
  case {
  x>=0 & x<=3 -> ensures emp & res=x;
  x>3 -> ensures emp & res=3;
  x<0 -> requires Loop ensures false;
  }
 */
/*@
infer [P1,Q1]
  requires P1(x) ensures Q1(x,res);
 */

{
  if (x==0) return 0;
  int ret = id2(x-1) + 1;
  if (ret > 3) return 3;
  return ret;
}

/*@
relation P2(int x).
relation Q2(int x, int y).
 */

int id2(int x)
/*
  case {
  x>=0 & x<=3 -> ensures emp & res=x;
  x>3 -> ensures emp & res=3;
  x<0 -> requires Loop ensures false;
  }
 */
/*@
infer [P2,Q2]
  requires P2(x) ensures Q2(x,res);
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
  if (result == 5) {
    __error();
  }
}
