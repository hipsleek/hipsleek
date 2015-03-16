data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

relation A(int n, int m, int z).

void append(node x, node y)
  infer [n,A]
  requires x::ll<n>*y::ll<m>
  ensures x::ll<z> & A(z,m,n);
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
