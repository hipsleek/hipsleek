/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1> // = q1 
	inv n >= 0;

/* delete a node from a doubly linked list */
void delete(node2 x, int a)
	requires x::dll<p, n> & n > a & a > 0 
	ensures x::dll<p, n-1>;
{
	node2 tmp;
	node2 tmp_null = null;

	if (a == 1) 
	{
		if (x.next.next != null)
		{
			x.next.next.prev = x;
			tmp = x.next.next;
			//x.next = tmp; //fail here
		}
		else
			x.next = tmp_null;
	}
	else {
		delete(x.next, a-1);
	}
}

/* delete a node from a doubly linked list */
void delete2(node2 x, int a)
	requires x::dll<p, n> & n > a & a > 0 
	ensures x::dll<p, n-1>;
{
	node2 tmp;
	node2 tmp_null = null;

	if (a == 1) 
	{
	    // fail
		if (x.next.next != null)
		{
			x.next.next.prev = x;
			tmp = x.next.next;
			x.next = tmp;
		}
		// else
			// x.next = tmp_null;
	}
	else {
		delete(x.next, a-1);
	}
}


/* append 2 doubly linked lists */
node2 append(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n>
	ensures res::dll<_, m+n>;
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
		    x = null; // fail here
			// x.next = null;
		}
		return x; 
	}
}

/* append 2 doubly linked lists */
node2 append2(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n>
	ensures res::dll<_, m+n>;
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
		return y; // fail here
        // return x; 
	}
}