data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

relation R(int n, int m, int v).

relation A(int v).

int length(node x)
  infer [R,v1]
  requires x::ll<n>@v1
  ensures R(res,n,v1);
  // R(res,n) = res=n
{
  if (x==null) return 0;
  else {
    int r = length(x.next);
    return 1+r;
  }
}

data cell {int val;}

int sum (cell i, cell j)
  requires i::cell<a>*j::cell<b>
  ensures  i::cell<a>*j::cell<b> & res=a+b;
{
  return i.val + j.val;
}

