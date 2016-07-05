data node {
	int val;
	node next;
}

lseg<n, p> ==
	self = p & n = 0 or
	self::node<_, q> * q::lseg<n-1, p>
	inv n>=0;

clist<n> ==
	self::node<_, q> * q::lseg<n-1, self>
	inv n>0;

lemma self::clist<n> <- self::lseg<n-1, q> * q::node<_, self>;

node insert (node x, int a)
	requires x::lseg<n, null> & Term[n]
	ensures res::lseg<n+1, null>;

	requires x::clist<_>@L & Loop
	ensures false;
{
	if (x == null)
		return new node(a, null);
	else {
		x.next = insert(x.next, a);
		return x;
	}
}
