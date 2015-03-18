/* doubly linked lists */

/* representation of a node */
data node2 {
  int val; 
  node2 prev;
  node2 next;  
}

/* view for a doubly linked list with size */
dll<p, n> == self = null & n = 0 
  or (exists v, q, m: self::node2<v ,p , q> * q::dll<self, m> & n = m + 1)
  inv n >= 0;

/* append 2 doubly linked lists */
void append(node2 x, node2 y)
  requires x::dll<q, m> * y::dll<p, n> & m>0
  ensures x::dll<q, m+n>;
{
  if (x.next == null) {
    x.next = y;
    if (y != null) {
      y.prev = x;
    }    
  } else {
    append(x.next, y);
  }
}


