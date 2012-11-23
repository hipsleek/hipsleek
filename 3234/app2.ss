
/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

lseg<p,n> == self = p & n = 0 
  or self::node<_, q> * q::lseg<p,n-1> 
  inv n >= 0;


void append(node x, node y)
  requires x::lseg<null,n1> * y::lseg<null,n2> & n1>0
  ensures x::lseg<null,n1+n2>;
  requires x::lseg<null,n1> & n1>0 
  ensures x::lseg<y,n1>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}





