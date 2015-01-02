data node {
  int val;
  node next;
}

ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;

relation P(int n).
  relation Q(int n, int m).

int length(node x)
  infer [P,Q]
  requires x::ll<n> & P(n)
  ensures x::ll<n> & Q(n,res);
{
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# bugs-ex20.ss

int length(node x)
  infer [P,Q]
  requires x::ll<n> & P(n)
  ensures x::ll<n> & Q(n,res);
{
  if (x==null) return 0;
  else return 1+length(x.next);
}

!!! fixcalc file name: fixcalc1.inf
!!! bottom_up_fp:[( Q(n,res), res=n_1407)]
!!! fixpoint:[( Q(n,res), res=n_1407, P(n), true)]
!!! REL POST :  Q(n,res)
!!! POST:  res=n_1407
!!! REL PRE :  P(n)

Why did we get the above, when fixcalc1.inf gave:

pls2nus@loris-laptop:~/code/default/tut/ex2$ fixcalc fixcalc1.inf 
# Q:={ ... };
(n >= 0 && n = res)

*/
