data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1>
	inv n >= 0;

sll<n, sm, lg> == self = null & n = 0 & sm <= lg 
	or (exists qs,ql: self::node<qmin, q> * q::sll<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin )
	inv n >= 0 & sm <= lg;

node insert2(node x, node vn)
	requires x::sll<n, sm, lg> *  vn::node<v, _>
	ensures res::sll<n+1, mi, ma> & mi=min(v, sm) & ma=max(v, lg);
{
	if (x==null) {
		vn = null;
		// vn.next = null;
    return vn;
	}
	else if (vn.val <= x.val) {
		vn.next = x;
		return vn;
    // return vn.next;
	}
	else {
		x.next = insert2(x.next, vn);
		return x;
	}
}
