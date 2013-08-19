/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,"n":n> == 
	self = null &["n":n = 0] or 
	self::node2<_ ,p , q> * q::dll<self, n1> & ["n":n1=n-1]
	inv true & ["n":n >= 0];

/* append 2 doubly linked lists */
void append2(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n> & ["n":m>0]
	ensures x::dll<q, n1> & ["n":n1=n+m];
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

