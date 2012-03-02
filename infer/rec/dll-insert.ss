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
     infer [x,A]
     requires x::dll<p, n> //& n>0 //&  x!=null  
     ensures x::dll<p, m> & A(m,n); 
{
  bool l = x.next == null;
  if (l)
			x.next = new node2(a, x, null);
		else 
      insert(x.next, a);
}
