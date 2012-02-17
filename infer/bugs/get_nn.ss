data node {
	int val;
	node next;
}

ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

//Inferred Pure :[ n!=1]
node get_next_next(node x)
  infer[n,m]
  requires x::ll<n> & x!=null
  ensures res::ll<m>;
{
  return x.next.next;
}
