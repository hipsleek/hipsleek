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

ls<n,p> == self = p & n = 0 
  or self::node<_, q> * q::ls<n-1,p> 
  inv n >= 0;


void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & n1>0 & Term[n1]
  ensures x::ll<n1+n2>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

/*
TODO : why two messages?
Termination checking result:
(35)->(40) (ERR: not bounded) 
(35)->(40) (ERR: not bounded) 
*/

int length(node x)
	//infer[n1]
  requires x::ll<n1> 
		& Term[-1+n1]
  ensures res=n1;
{
	if (x == null)
      return 0;
	else 
	  return 1+length(x.next);
}



