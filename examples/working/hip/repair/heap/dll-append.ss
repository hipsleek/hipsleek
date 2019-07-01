data node2 {
	node2 prev;
	node2 next;	
}

dll<p,n> == self = null & n = 0 
  or (exists q: self::node2<p , q> * q::dll<self, n-1> & n > 0);

void append2(node2 x, node2 y)
	requires x::dll<a, m> * y::dll<b, n> & m>0 & n > 0
	ensures x::dll<a, m+n>;
{
	if (x.next == null) {
		// x.next = y;
    x.next = y.next;
    y.prev = x;
	}
	else {
		append2(x.next, y);
	}
}


 