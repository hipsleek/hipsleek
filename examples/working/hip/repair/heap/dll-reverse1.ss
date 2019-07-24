data node2 {
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<p , q> * q::dll<self, n-1> & n > 0;

node2 reverse(node2 xs, node2 ys)
	requires xs::dll<p, n> * ys::dll<q, m>
	ensures res::dll<_, n+m>;
{
	if (xs != null) {
		node2 tmp;
		tmp = xs.next;
    if (tmp != null)  tmp.prev = null;
		// xs.next = ys;
		xs = ys;
    if (ys != null) ys.prev = xs;
		return reverse(tmp, xs);
	}
  else return ys;
}
