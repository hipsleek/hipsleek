/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

dll<p,"n":n> == 
	self = null &["n":n = 0] or 
	self::node2<_ ,p , q> * q::dll<self, n1> & ["n":n1=n-1]
	inv true & ["n":n >= 0];



/* delete a node from a doubly linked list */
void delete(node2 x, int a)
	requires x::dll<p, n> & ["n":n > a & a > 0] 
	ensures x::dll<p, n1> & ["n":n1=n-1];
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

/* NOT WORKING */
void delete1(node2 x, int a)
	requires x::dll<p, n> & ["n":n > a > 0] 
	ensures x::dll<p, n1> & ["n":n1=n-1];

{
	node2 tmp;

	if (a == 1) 
	{
		if (x.next.next != null)
		{
			x.next.next.prev = x;
		}

		tmp = x.next.next;
		x.next = tmp;
	}
	else
		delete1(x.next, a-1);
}


