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




void test_del2(node2 x, node2 tmp2)
	requires 	x::node2<_,_,_> * tmp2::dll<x, _> & tmp2!=null
			or	x::node2<_,_,_> & tmp2=null
	ensures		x::dll<_,_>;
{
	if (tmp2 != null) {
		tmp2.prev = x;
	}
	x.next = tmp2;
}

