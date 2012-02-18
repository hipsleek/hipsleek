data node {
	int val;
	node next;
}

ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});

/* return the tail of a singly linked list */
relation GN(bag a, bag b, bag c).
node get_next(ref node x)
  infer[GN]
  requires x::ll2<n,S> & x!=null
  ensures x'::ll2<1,S1> * res::ll2<n-1,S2> & GN(S,S1,S2);//S  = union(S1, S2)//'
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}
