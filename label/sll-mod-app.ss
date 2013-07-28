/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<"n":n> == 
	self = null & ["n":n = 0] or 
	self::node2<_ ,p , q> * q::dll<n1> & ["n":n1=n-1]
	inv true & ["n":n >= 0];

/* append 2 doubly linked lists */
node2 append(node2 x, node2 y)
	requires x::dll<m> * y::dll<n>
	ensures res::dll<n1> & ["n":n1=n+m];
{
	node2 tmp;

	if (x == null)
		return y;
	else
	{
		x.next = append(x.next, y);
		return x; 
	}
}

