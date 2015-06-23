/* These examples don't directly compare to the previous ones. */

relation R(int x,int a).

int nondet_int()
  requires Term[]
  ensures true;

void loo (ref int x, int a)
     infer [R]
     requires R(x,a)
     ensures true;
{
  if (a == 10 && x > 0) {
    x = x - 1;
    loo(x, a);
  } else if (x > 0) {
    a = 10;
    loo(x, 10);
  }
}

/*
# ex23.ss

[RELDEFN R: ( a=10 & a'=10 & x=x'+1 & 0<=x' & R(x,a)) -->  R(x',a'),
RELDEFN R: ( a'=10 & 1<=x' & a!=10 & R(x',a)) -->  R(x',a')]

Both cases, param flow is 'unknown'.
a may stay the same, or it may be set to 10.
x may decrement or it may not.

 */
