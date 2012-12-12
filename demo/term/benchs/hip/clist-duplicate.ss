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

node duplicate (node x)
	requires x::lseg<n, null> & Term[n]
	ensures res::lseg<2*n, null>;

	requires x::clist<n> & Loop
	ensures false;
{
	if (x == null)
		return null;
	else {
		node tmp = new node (x.val, null);
		tmp.next = duplicate(x.next);
		x.next = tmp;
		return x;
	}
}
