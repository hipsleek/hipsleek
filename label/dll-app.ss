/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<"p":p,"n":n> == 
	true&["p":self = null; "n":n = 0] or 
	(exists q1: self::node2<_ ,p , q> * q::dll<self, n1> & ["p":self = q1; "n":n1=n-1])
	inv true & ["n":n >= 0];



/* append 2 doubly linked lists */
node2 append(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n>
	ensures res::dll<_, n1> & ["n":n1=n+m];
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

