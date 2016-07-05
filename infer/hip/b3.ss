/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

/* append two singly linked lists */
void hd(node x)
  infer [n1] 
  requires x::ll<n1>
  ensures x::ll<m> & m>1; 
  // OK to fail
{    
  int v;
  v = x.val;
  x = x.next;
}


