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

