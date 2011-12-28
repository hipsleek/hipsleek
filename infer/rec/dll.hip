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

relation A(int x, int y).
relation B(int x, int y).
relation C(int x, int y, int z).

void insert(node2 x, int a)
     infer @pre[x,A]
     requires x::dll<p, n> //& n>0 //&  x!=null  
     ensures x::dll<p, m> & A(m,n); 
{
  bool l = x.next == null;
  if (l)
			x.next = new node2(a, x, null);
		else 
      insert(x.next, a);
}


/* delete a node from a doubly linked list */
void delete(node2 x, int a)
        infer @pre[a,B]  
        requires x::dll<p, n> & B(n,a) //n > a & a > 0 
	// why does is infer a<2?
	ensures x::dll<p, n-1>;
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


/* append 2 doubly linked lists */
node2 append(node2 x, node2 y)
      infer @pre[C]
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



