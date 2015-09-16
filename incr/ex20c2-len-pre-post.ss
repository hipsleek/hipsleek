/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<> == self = null  
	or self::node<_, q> * q::ll<> 
  inv true;


	
HeapPred P(node x).


int length(node x)
  infer [@shape_post,@classic]
  requires x::ll<>
  ensures true;
{    
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# ex20c2.ss

[ GP_1615(x_1643) ::= x_1643::ll<>@M(4,5)]

*/
