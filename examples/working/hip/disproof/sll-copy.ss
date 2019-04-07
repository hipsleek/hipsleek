/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

node copy(node x)
requires x::ll<n>
ensures x::ll<n> * res::ll<n>;
{
  if (x == null) return x;
  else {
      node tmp = copy(x.next);
      node n = new node(x.val, tmp);
      return n.next;
  }
}