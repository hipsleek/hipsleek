/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p, n, S> == self = null & n = 0 & S = {}
  or self::node2<v ,p , q> * q::dll<self, n-1, S1> & S = union({v}, S1) 
	inv n >= 0;

void insert(node2 x, int a)
  requires x::dll<p, n, S> & n>0  
  ensures x::dll<p, n+1, S1> & S1 = union(S, {a}); 
{
	bool l = x.next == null;
	if (l)
		x.next = new node2(a, x, null);
	else 
		insert(x.next, a);
}

/* delete a-th node from a doubly linked list */
void delete(node2 x, int a)
	requires x::dll<p, n, _> & n > a & a > 0 
	ensures x::dll<p, n-1, _>;
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

/* append 2 doubly linked lists */
node2 append(node2 x, node2 y)
	requires x::dll<q, m, S1> * y::dll<p, n, S2>
	ensures res::dll<_, m+n, S> & S = union(S1, S2);
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
	requires x::dll<q, m, S1> * y::dll<p, n, S2>
	ensures res::dll<_, m+n, S> & S = union(S1, S2);	
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
	requires x::dll<q, m, S1> * y::dll<p, n, S2> & m>0
	ensures x::dll<q, m+n, S> & S = union(S1, S2);
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
