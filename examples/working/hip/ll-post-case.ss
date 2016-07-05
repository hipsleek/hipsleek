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

/* append two singly linked lists */

void append2(node x, node y)
  requires x::ll<n1> * y::ll<n2> & n1>0 & n2>0 // & x!=null // & n1>0 //x!=null // & n1>0 & x != null
  ensures 
	case {
		n1>0 -> 
			case{ n2>0 -> [] x::ll<m> & m=n1+n2; 
				  n2<=0 -> [] x::ll<m> & m=n1+n2;
				};
		n1<=0 -> [] x::ll<m> 
			case{ n2>0 -> []  m=n1+n2; 
				  n2<=0 -> [] m=n1+n2;
				};
		};
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}
