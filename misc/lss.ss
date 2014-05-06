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


ls<p> == self = p  
	or self::node<_, q> * q::ls<p> & self!=p 
  inv true;

lss<p,n> == self = p & n=0
  or self::node<_, q> * q::lss<p,n-1> & self!=p 
  inv n>=0;


void append(node x, node y)
  /*
  // cannot verify as we do not know if y points into first segment 
  requires x::ls<null> * y::ls<q> & x!=null 
  ensures x::ls<y> * y::ls<q>;
  // BUGS : complex lemma should handle below
  requires x::ls<null> * y::ls<q> & x!=null & y!=q 
  ensures x::ls<y> * y::ls<q>;
  */
  requires x::ll<n1> * y::ll<n2> & n1>0 
  ensures x::ll<n1+n2>;
  requires x::ls<null> * y::ls<null> & x!=null 
  ensures x::ls<null>;
  requires x::ls<null> * y::ls<q> * q::node<a,b> & x!=null  
  ensures x::ls<q> *q::node<a,b>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

bool randBool () 
  requires true
 ensures true;

// why split not allowed as a name? already exists?
node split2 (node x, node y)
  requires x::ls<y>
  ensures res::ls<y>;
/*
  requires x::ls<r> * r::ls<y>
  ensures res=r;
*/
  requires x::lss<y,n>
  ensures res::lss<y,m> & m<=n;
{
   if (x==y) 
    return x;
   else {
     if (randBool()) return x;
     else return split2(x.next, y);
   } 
}





