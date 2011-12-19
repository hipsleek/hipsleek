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
  infer @pre [n1]
  requires x::ll<n1> * y::ll<n2>
  ensures x::ll<m> & m=n1+n2;
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

// TODO : Below has 4 similar post-conditions which will be expensive
// Need a way to abstract common post.
/*
           q_540::ll<flted_14_538>@M[Orig] * x::ll<m_591>@M[Orig][LHSCase] &
           n2=(m_591 - flted_14_538) - 1 & n1=flted_14_538+1 & q_540=null & 
           0<=n1 & 0<=n2 & {FLOW,(20,21)=__norm}
           or x::ll<m_592>@M[Orig][LHSCase] & n2=(m_592 - flted_14_538) -
              1 & n1=flted_14_538+1 & 0<=flted_14_538 & flted_14_538<m_592 & 
              q_540!=null & 0<=n1 & 0<=n2 & {FLOW,(20,21)=__norm}
           or q_540::ll<flted_14_538>@M[Orig] * 
              x::ll<m_593>@M[Orig][LHSCase] & n2=(m_593 - flted_14_538) -
              1 & n1=flted_14_538+1 & q_540=null & 0<=n1 & 0<=n2 &
              {FLOW,(20,21)=__norm}
           or x::ll<m_594>@M[Orig][LHSCase] & n2=(m_594 - flted_14_538) -
              1 & n1=flted_14_538+1 & 0<=flted_14_538 & flted_14_538<m_594 & 
              q_540!=null & 0<=n1 & 0<=n2 & {FLOW,(20,21)=__norm}
*/


