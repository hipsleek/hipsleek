data node{
	int val;
	node next;
}

inflist<n,p> == self = p & n = 0
	or self::node<_,q> * q::inflist<n-1,p> & self != p
inv n >= 0;

node remove(node x, int k)
requires x::inflist<\inf,null> & 0 <= k <= \inf
ensures x::inflist<k,res> * res::inflist<\inf,null>;
{
	if (x == null) return x;
	else {
		if (k == 0) return x;
		else return remove(x.next,k-1);
	}
}

void append(node x, node y)
  requires x::inflist<n,null> * y::inflist<\inf,null> & x!=null 
  ensures x::inflist<\inf,null>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

