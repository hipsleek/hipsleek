/* singly linked lists */

/* to complete */

/* representation of a node */
data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


//relation A(int x, int y).
relation B(int x, int y).

/* delete a node from a doubly linked list */
void delete(node x, int a)
        infer @pre[B]  
        requires x::dll<p, n> & n > a & a > 0 
	    ensures x::dll<m> & B(m,n); //m=n-1;
{
	node tmp;
	node tmp_null = null;

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
