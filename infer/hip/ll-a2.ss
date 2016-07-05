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
  infer  [n1]
  requires x::ll<n1> * y::ll<n2>
  ensures x::ll<m> & m=n1+n2;
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

// only infers pre here
/*
NEW SPECS:  EBase exists (Expl)(Impl)[n1; n2](ex)x::ll<n1>@M[Orig][LHSCase] * 
       y::ll<n2>@M[Orig][LHSCase] & n1!=0 & {FLOW,(20,21)=__norm}
         EAssume 1::
           EXISTS(m_591: x::ll<m_591>@M[Orig][LHSCase] & m_591=n2+n1 & 
           0<=n1 & 0<=n2 & {FLOW,(20,21)=__norm})

*/


