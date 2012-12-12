data node {
	int val;
	node next;
}

lseg<n, p, S> ==
	self = p & n = 0 & S = {} or
	self::node<v, q> * q::lseg<n-1, p, S1> & S = union(S1, {v})
	inv n>=0;

clist<n, S> ==
	self::node<v, q> * q::lseg<n-1, self, S1> & S = union(S1, {v})
	inv n>0;

lemma self::clist<n, S> & S = union(S1, {v}) <- self::lseg<n-1, q, S1> * q::node<v, self>;

int length (node x)
	requires x::lseg<n, null, _>@L & Term[n]
	ensures res=n;

	requires x::clist<_, _>@L & Loop
	ensures false;
{
	if (x == null)
		return 0;
	else
		return 1 + length(x.next);
}

node duplicate (node x)
	requires x::lseg<n, null, S> & Term[n]
	ensures res::lseg<2*n, null, S>;

	requires x::clist<n, _>@L & Loop
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

node remove (node x, int v)
	requires x::lseg<n, null, S> & Term[n]
	case {
		(v notin S) -> ensures res::lseg<n, null, S>;
		(v in S) -> ensures res::lseg<n-1, null, S1> & S = union(S1, {v});
	}
		
	requires x::clist<n, S> & (v notin S) & Loop
	ensures false;
	
{
	if (x == null)
		return null;
	else {
		if (x.val == v)
			return x.next;
		else {
			x.next = remove(x.next, v);
			return x;
		}
	}
}

node insert (node x, int v)
	requires x::lseg<n, null, S> & Term[n]
	ensures res::lseg<n+1, null, S1> & S1 = union(S, {v});

	requires x::clist<_, _>@L & Loop
	ensures false;
{
	if (x == null)
		return new node(v, null);
	else {
		x.next = insert(x.next, v);
		return x;
	}
}
