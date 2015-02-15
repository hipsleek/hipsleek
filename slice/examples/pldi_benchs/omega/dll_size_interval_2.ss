/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p, n, mn, mx> == 
	self = null & n = 0 & mn = mx
	or self::node2<x, p, q> * q::dll<self, n-1, mn, mx> & mn <= x < mx
	inv n >= 0 & mn <= mx;

void insert(node2 x, int a)
  requires x::dll<p, n, mn, mx> & n>0
  ensures x::dll<p, m, mn1, mx1> & m=n+1 & mn1 = min(a, mn) & mx1 = max(a, mx); 
  
{
	if (x.next == null)
		x.next = new node2(a, x, null);
	else 
		insert(x.next, a);
}

/* delete a_th node from a doubly linked list */
void delete(node2 x, int a)
	requires x::dll<p, n, mn, mx> & n > a & a > 0 
	ensures x::dll<p, n-1, mn, mx>;
{
	node2 tmp;
	node2 tmp_null = null;

	if (a == 1) 
	{
		if (x.next.next != null)
		{
			x.next.next.prev = x;
			tmp = x.next.next;
			x.next = tmp;
		}
		else
			x.next = tmp_null;
	}
	else {
		delete(x.next, a-1);
	}
}

void delete1(node2 x, int a)
	requires x::dll<p, n, mn, mx> & n > a > 0 
	ensures x::dll<p, n-1, mn, mx>;
{
	if (a == 1) 
	{
		node2 l = x.next.next;
		if (l!= null)
		{
			l.prev = x;
     	}
		x.next = l;
	}
	else
	{
		delete1(x.next, a-1);
	}
}

/* append 2 doubly linked lists */
node2 append(node2 x, node2 y)

	requires x::dll<q, m, mn1, mx1> * y::dll<p, n, mn2, mx2>
	case {
		x = null -> ensures res = y;
		x != null -> case {
			y = null -> ensures res::dll<q, m, mn1, mx1>;
			y != null -> ensures res::dll<q, m+n, mn, mx> & mn = min(mn1, mn2) & mx = max(mx1, mx2);
		}
	}
{
	node2 tmp;

	if (x == null)
		return y;
	else
	{ 	
		tmp = x.next;
		tmp = append(tmp, y);

		if (tmp != null)
		{
			x.next = tmp; 
			tmp.prev = x;
		}
		else {
			x.next = null;
		}

		return x; 
	}
}

node2 append1(node2 x, node2 y)

	requires x::dll<q, m, mn1, mx1> * y::dll<p, n, mn2, mx2>
	case {
		x = null -> ensures res = y;
		x != null -> case {
			y = null -> ensures res::dll<q, m, mn1, mx1>;
			y != null -> ensures res::dll<q, m+n, mn, mx> & mn = min(mn1, mn2) & mx = max(mx1, mx2);
		}
	}	

{
	if (x == null)
		return y;
	else
	{	
		node2 tmp = append1(x.next, y);
		if (tmp != null)
			tmp.prev = x;
		x.next = tmp;

		return x;
	}
}

/* append 2 doubly linked lists */
void append2(node2 x, node2 y)
	
	requires x::dll<q, m, mn1, mx1> * y::dll<p, n, mn2, mx2> & m > 0
	case {
		y = null -> ensures x::dll<q, m, mn1, mx1>;
		y != null -> ensures x::dll<q, m+n, mn, mx> & mn = min(mn1, mn2) & mx = max(mx1, mx2);
	}	

{
	node2 tmp;

	if (x.next == null) {
		x.next = y;
		if (y != null) {
			y.prev = x;
		}		
	}
	else {
		append2(x.next, y);
	}
}
