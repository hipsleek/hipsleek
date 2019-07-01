/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1> & n > 0;

node2 copy(node2 x)
requires x::dll<p, n>
ensures x::dll<p, n> * res::dll<p, n>;
{
  if (x == null) return x;
  else {
      node2 tmp = copy(x.next);
      node2 tmp2 = x.prev;
      node2 n = new node2(x.val, tmp2, tmp);
      if (tmp != null) tmp.prev = n;
      return n.next;
  }
}