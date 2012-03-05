
/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

lseg<p,n> == self = p & n = 0 
  or self::node<_, q> * q::lseg<p,n-1> 
  inv n >= 0;

clist<n> == self::node<_,q> * q::lseg<self,n-1>
  inv n >= 1;

void append(node x, node y)
  requires x::lseg<null,n> & n>0 
  ensures x::lseg<y,n>;
  requires x::lseg<null,n> & n>0 & x=y
  ensures x::clist<n>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}





