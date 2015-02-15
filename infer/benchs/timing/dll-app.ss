/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size and bag */
dll<p,n,S> == self = null & n = 0 & S={}
  or self::node2<v ,p , q> * q::dll<self, n-1, S1> & S=union(S1, {v})
	inv n >= 0;

relation APP(bag a, bag b, bag c).
node2 append(node2 x, node2 y)
  infer [APP]
	requires x::dll<q, m, S1> * y::dll<p, n, S2>
	ensures res::dll<_, t, S> & t=m+n & APP(S,S1,S2); // S=union(S1,S2)

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
