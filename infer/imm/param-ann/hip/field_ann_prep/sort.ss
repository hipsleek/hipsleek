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

lemma "L1" self::sll<n, mi,ma> -> self::ll<n>;

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

/* transform a normal singly linked list in a sorted list */
void insertion_sort(node x, ref node y)
	requires x::ll<n> * y::sll<m1, ys1, yl1>
	ensures y'::sll<n + m1, _, _> * x::ll<n>;//'

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}

/* transform a normal singly linked list in a sorted list */
node insertion_sort2( node x)
  requires x::ll<n> 
  ensures res::sll<n, _, _> ;
{
  if (x.next == null) return x;
  else
	{      
      x.next = insertion_sort2(x.next);
      return insert2(x.next, x);
	}
}



int insert3(ref node x, node vn)
	requires x::sll<n, sm, lg> *  vn::node<v, _>
	ensures res::sll<n+1, mi, ma> & mi=min(v, sm) & ma=max(v, lg);
{
	if (x==null) {
		return vn.val;
	}
	else if (vn.val <= x.val) {
      left_shift_val(x);
      return vn.val;
	}
	else {
		x.next = insert2(x.next, vn);
		return x;
	}
}

/* transform a normal singly linked list in a sorted list */
void insertion_sort_ann(ref node x)
  requires x::ll<n> 
  ensures res::sll<n, _, _>;
{
  if (x.next != null) {
      insertion_sort_ann(x.next);
      x.val = insert2(x.next, x);
  }
}

/* transform a normal singly linked list in a sorted list */
/*void insertion_sort(node x, ref node y)

  requires x::ll<n> * y::sll<m1, ys1, yl1>
  ensures y'::sll<n + m1, _, _> * x::ll<n>;

{
	if (x != null)
	{   insertion_sort(x.next, y);
		y = insert(y, x);
		
	}
}*/


