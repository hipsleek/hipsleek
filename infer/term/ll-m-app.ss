data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

void append(node x, node y)
  requires x::ll<n>*y::ll<m> & n>0 & Term[2*n+1]
  ensures x::ll<z> & z=m+n;
{
  app2(x,y);
}

void app2(node x, node y)
  requires x::ll<n>*y::ll<m> & x!=null & Term[2*n]
  ensures x::ll<z> & z=m+n;
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
