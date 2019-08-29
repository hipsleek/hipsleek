// strong specs

data node {
	int val; 
	node next;	
}

sll<n, sm, lg> == self = null & n = 0
or (exists qs, q:
 self::node<sm, q> * q::sll<n-1, qs, lg> & sm <= qs & n > 0 & qs <= lg);

node insert2(node x, node vn)
 requires vn::node<v,_> & x = null ensures x::sll<1, v,v>;
	requires x::sll<n, sm, lg> *  vn::node<v, _> & n > 0
	ensures res::sll<n+1, mi, ma> & mi=min(v, sm) & ma=max(v, lg);
{
	if (x==null) {
		vn.next = null;
    return vn;
	} else
  if (vn.val <= x.val) {
    vn.next = x;
		return vn;
	}
	else {
    x.next = insert2(x.next, vn);
		// x.next = insert2(x.next, vn.next);
		return x;
	}
}

// sll<n, sm, lg> == self = null & n = 0 & sm <= lg 
// 	or (exists qs,ql, qmin, q:
//   self::node<qmin, q> * q::sll<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin)
// 	inv n >= 0 & sm <= lg;

