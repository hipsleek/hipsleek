data node2 {
	node2 prev;
	node2 next;	
}

dll<p,n> == self = null & n = 0 
  or (exists q: self::node2<p , q> * q::dll<self, n-1> & n > 0)
	inv n >= 0;

HeapPred P(node2 x, node2 y).
HeapPred Q(node2 x, node2 y).

void fcode(node2 x, node2 y)
   requires P(x, y)
   ensures Q(x, y);

void append2(node2 x, node2 y)
	requires x::dll<q, m> * y::dll<p, n> & m>0
	ensures x::dll<q, m+n>;
{
	if (x.next == null) {
    fcode(x,y);
    if (y != null)
       y.prev = x;
	}
	else {
		append2(x.next, y);
	}
}
