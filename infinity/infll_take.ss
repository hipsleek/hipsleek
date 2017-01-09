data node{
	int val;
	node next;
}

inflist<n> == self = null & n = 0
	or self::node<_,q> * q::inflist<n-1> 
inv n >= 0;

node take(node x, int k)
  requires x::inflist<\inf>
  ensures  res::inflist<k> * x::inflist<\inf> ;
{
  node y;
  if (k == 0) return null;
  else {
    y = new node(x.val, null);
    y.next = take (x.next, k-1);
    return y;
  }
}
