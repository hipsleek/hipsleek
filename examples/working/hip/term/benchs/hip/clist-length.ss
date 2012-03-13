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

int length (node x)
	requires x::lseg<n, null>@L & Term[n]
	ensures res=n;

	requires x::clist<_>@L & Loop
	ensures false;
{
	if (x == null)
		return 0;
	else
		return 1 + length(x.next);
}
