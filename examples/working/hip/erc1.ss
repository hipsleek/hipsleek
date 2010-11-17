data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
	inv n >= 0;

node id(node x)
  requires x::ll<n> & x!=null
  ensures res::ll<n> & n>0;
{    
  return x;
}
