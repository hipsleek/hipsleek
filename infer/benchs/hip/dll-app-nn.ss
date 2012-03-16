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

relation D(int x, int y, int z, node2 m, node2 n, node2 p).

void append2(node2 x, node2 y)
  infer  [D]
	requires x::dll<q, m> * y::dll<p, n> & m>=1
	ensures x::dll<r, t> & D(t,m,n,r,p,q);

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
