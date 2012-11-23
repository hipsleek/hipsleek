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


void append(node x, node y)
  requires x::ll<n> * y::ll<m> & n>0 & Term[n]
  ensures x::ll<n+m>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

ls<n,p> == self = p & n = 0 
  or self::node<_, q> * q::ls<n-1,p> 
  inv n >= 0;

clist<n> == self::node<_,q>*q::ls<n-1,self>
  inv n>0;

lemma self::clist<n> <- self::ls<n-1,q>*q::node<_,self>;

int length(node x)
  requires x::ls<n,null>@L & Term[n]
  ensures res=n;
  requires x::clist<_> & Loop
  ensures false;
{
	if (x == null)
      return 0;
	else 
	  return 1+length(x.next);
}



