data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

relation A(int n, int m, int z).

void append(node x, node y)
  infer @pre [x,A]
  variance [c,p]@{n,m}
  requires x::ll<n>*y::ll<m> & n>0 
  ensures x::ll<z> & z=m+n;
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
