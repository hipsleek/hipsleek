/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

dll1<p> == self = null
  or self::node2<_ ,p , q> * q::dll1<self> 
  inv true;

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1> // = q1 
	inv n >= 0;

relation C(int x, int y, int z).


/* append 2 doubly linked lists */
node2 append(node2 x, node2 y)
  infer [C]
  requires x::dll<q, m> * y::dll<p, n>
  ensures res::dll<_, t> & C(t,m,n);

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

relation D(int x, int y, int z).

void append2(node2 x, node2 y)
  infer  [D]
	requires x::dll<q, m> * y::dll<p, n> & m>=1
	ensures x::dll<q, t> & D(t,m,n);

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
