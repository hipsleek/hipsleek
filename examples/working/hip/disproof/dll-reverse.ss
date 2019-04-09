data node2 {
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<p , q> * q::dll<self, n-1> & n > 0;

void reverse(node2@R xs, node2@R ys)
	requires xs::dll<p, n> * ys::dll<q, m>
	ensures ys'::dll<_, n+m> & xs' = null;
{
	if (xs != null) {
		node2 tmp;
		tmp = xs.next;
    // if (tmp != null)  tmp.prev = null;
    if (tmp != null)  tmp.next = null;
		xs.next = ys;
    // if (ys != null) ys.prev = xs;
    if (ys != null) ys.prev = xs.next;
		ys = xs;
		xs = tmp;
		// reverse(xs, ys);
    reverse(xs, ys.next);
	}
}
