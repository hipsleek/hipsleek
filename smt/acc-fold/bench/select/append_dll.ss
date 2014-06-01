/* doubly linked lists */

/* representation of a node */
data node2 {
  node2 prev;
  node2 next;  
}

/* view for a doubly linked list with size */
dll<p> == self = null 
  or (exists q: self::node2<p, q> * q::dll<self>);

/* append 2 doubly linked lists */
void append(node2 x, node2 y)
  requires x::dll<q> * y::dll<p> & x!=null
  ensures x::dll<q>;

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

