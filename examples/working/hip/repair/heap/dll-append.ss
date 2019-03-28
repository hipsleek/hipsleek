data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1>
	inv n >= 0;

void append2(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n> & m>0
	ensures x::dll<q, m+n>;

{
	if (x.next == null) {
		x.next = y.next;
    // x.next = y;
		if (y != null) {
			y.prev = x;
		}		
	}
	else {
		append2(x.next, y);
	}
}
