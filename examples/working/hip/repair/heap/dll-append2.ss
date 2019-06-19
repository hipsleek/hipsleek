data node2 {
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or (exists q: self::node2<p , q> * q::dll<self, n-1>);

void append2(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n> & m>0
	ensures x::dll<q, m+n>;
{
	if (x.next == null) {
    x.next = y;
    // fcode()
    if (y != null) x.next = y;
	}
	else {
		append2(x.next, y);
	}
}