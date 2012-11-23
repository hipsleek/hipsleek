/* LOC: 107 */
/* sorted lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1>
	inv n >= 0;

/* view for a sorted list */
sll<n, sm, lg> == self = null & n = 0 & sm <= lg 
	or (exists qs,ql: self::node<qmin, q> * q::sll<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin )
	inv n >= 0 & sm <= lg;

/* insert an element in a sorted list */
node insert(node x, int v)

	requires x::sll<n, sm, lg>
	ensures res::sll<n + 1, mi, ma> & mi = min(v, sm) & ma = max(v, lg); 

{
	node tmp;

	if (x == null)
		return new node(v, null);
	else
	{
		if (v <= x.val)
			return new node(v, x);
		else
		{
			tmp = x.next;
			x.next = insert(tmp, v);
			return x;
		}
	}
}


node insert2(node x, node vn)
	requires x::sll<n, sm, lg> *  vn::node<v, _>
	ensures res::sll<n+1, mi, ma> & mi=min(v, sm) & ma=max(v, lg);
{
	if (x==null) {
		vn.next = null;
		return vn;
	}
	else if (vn.val <= x.val) {
		vn.next = x;
		return vn;
	}
	else {
		x.next = insert2(x.next, vn);
		return x;
	}
}

/* delete a node from a sorted list */
node delete(node x, int v)

	requires x::sll<n, xs, xl>
	ensures res::sll<nres, sres, lres> & sres >= xs & lres <= xl & n-1 <= nres <= n;

{
	node tmp; 

	if (x != null)
		if (v < x.val)
			return x;
		else
			if (v == x.val)
				return x.next;
			else
			{
				tmp = x.next;
				x.next = delete(tmp, v);
				return x;
			}
	else
		return null;
}

/* get the tail of a sorted list */
node get_tail(node x)

	requires x::sll<n, xs, xl> & x != null
	ensures res::sll<n-1, sres, lres> & sres >= xs & lres <= xl; 

{
	return x.next;
}

/* transform a normal singly linked list in a sorted list */
void insertion_sort(node x, ref node y)

	requires x::ll<n> * y::sll<m1, ys1, yl1>
	ensures y'::sll<n + m1, _, _> * x::ll<n>;

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}

void id(int x)
	requires true ensures true;
{
	int n = 1; 
	n++;
	id(n);
}
