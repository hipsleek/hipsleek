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

//relation A(int x, int y).
relation B(int x, int y).

/* delete a node from a doubly linked list */
void delete(node2 x, int a)
    infer [B]  
    // this pre may be hard to infer; let us focus
    // first on inferring post; Currently I got empty FIXPOINT
    // can we try a simpler example using singly linked list?
    requires x::dll<p, n> & n > a & a > 0 //
	// why does is infer a<2?
	ensures x::dll<p, m> & B(m,n); //m=n-1;
{
	node2 tmp;
	node2 tmp_null = null;

	if (a == 1) 
	{
		if (x.next.next != null)
		{
			x.next.next.prev = x;
			tmp = x.next.next;
			x.next = tmp;
		}
		else
			x.next = tmp_null;
	}
	else {
		delete(x.next, a-1);
	}
}
