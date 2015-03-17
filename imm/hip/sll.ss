/* sorted lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll<n,a1,a2> == self = null & n = 0 
  or self::node<_@a1, q@a2> * q::ll<n-1,a1,a2>
	inv n >= 0;

/* view for a sorted list */
sll<n, sm, lg, a1, a2> == self = null & n = 0 & sm <= lg 
  or (exists qs,ql: self::node<qmin@a1, q@a2> * q::sll<n-1, qs, ql, a1, a2> & qmin <= qs & ql <= lg & sm <= qmin )
	inv n >= 0 & sm <= lg;

/* insert an element in a sorted list */
node insert(node x, int v)

  requires x::sll<n, sm, lg,@L,@M>
  ensures res::sll<n + 1, mi, ma,@A,@M> & mi = min(v, sm) & ma = max(v, lg); 

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
  requires x::sll<n, sm, lg,@L,@M> *  vn::node<v, _>
  ensures res::sll<n+1, mi, ma,@A,@M> & mi=min(v, sm) & ma=max(v, lg);
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

  requires x::sll<n, xs, xl,@L,@M>
  ensures res::sll<nres, sres, lres,@A,@M> & sres >= xs & lres <= xl & n-1 <= nres <= n;

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

  requires x::sll<n, xs, xl,@A,@L> & x != null
  ensures res::sll<n-1, sres, lres,@A,@A> & sres >= xs & lres <= xl; 

{
	return x.next;
}

/* transform a normal singly linked list in a sorted list */
/*
void insertion_sort(node x, ref node y)

  requires x::ll<n,@L,@M> * y::sll<m1, ys1, yl1,@L,@M>
	ensures y'::sll<n + m1, _, _, @A,@M> * x::ll<n,@A,@M>;

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}
*/
void id(int x)
	requires true ensures true;
{
	int n = 1; 

	n ++;
	id(n);
}
