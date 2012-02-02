data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

ranking r(int n, int m).

void append(node x, node y)
  infer @pre [r]
  requires x::ll<n>*y::ll<m> & n>0 & Term[r(n,m)]
  ensures x::ll<z> & z=m+n;
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
