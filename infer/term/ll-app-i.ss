data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

ranking r(int n, int m).

relation p(int n, int m).


void append(node x, node y)
  infer [r,p,n]
  requires x::ll<n>*y::ll<m> & Term[r(n,m)]
  ensures x::ll<z> & p(z,n);
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
