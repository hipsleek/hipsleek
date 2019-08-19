data node2 {
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<p , q> * q::dll<self, n-1> & n > 0;

node2 copy(node2 x)
requires x::dll<p, n>
ensures x::dll<p, n> * res::dll<p, n>;
{
  if (x == null) return x;
  else {
      node2 tmp;
      tmp = copy(x.next);
      node2 nd;
      nd = new node2(x.prev, tmp);
      if (tmp != null) tmp.prev = nd;
      return nd.next;
      // return nd;
  }
}

