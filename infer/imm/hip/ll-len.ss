data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

relation R(int n, int m).

int length(node x)
  infer [v1]
  requires x::ll<n>@v1
  ensures res=n;
{
  if (x==null) return 0;
  else {
    int r = length(x.next);
    return 1+r;
  }
}

data cell {int val;}

int sum (cell i, cell j)
  infer [v1, v2]
  requires i::cell<a>@v1*j::cell<b>@v2
  ensures  res=a+b;
{
  return i.val + j.val;
}

