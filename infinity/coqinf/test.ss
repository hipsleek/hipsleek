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

relation CPY(int k, int m).
node list_copy(node x)
  infer[CPY]
  requires x::ll<n> 
  ensures x::ll<n> * res::ll<m> & CPY(m,n); 
{
  node tmp;
  if (x != null) {
    tmp = list_copy(x.next);
    return new node (x.val, tmp) ;
  }
  else
    return null;
}


void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null; // '

