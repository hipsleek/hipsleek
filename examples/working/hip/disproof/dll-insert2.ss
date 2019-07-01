data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1> & n > 0;

void insert(node2 x, int a)
  requires x::dll<p, n> & n>0
  ensures x::dll<p, n+1>; 
{
  if (x.next != null)
  x.next = new node2(a, x, null);
	else insert(x.next, a);
}
