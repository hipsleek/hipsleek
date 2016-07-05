data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

void append(node x, node y)
  requires x::ll<n> * y::ll<m> & n!=0
  ensures x::ll<n+m>;
{
  if (x.next!=null) append(x.next, y);
  else x.next = y;
}
