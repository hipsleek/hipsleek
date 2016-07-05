
/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

list<> == self = null 
	or self::node<_, q> * q::list<> 
  inv true;


void append(node x, node y)
  requires x::list<> * y::list<> & x!=null
  ensures x::list<>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}





