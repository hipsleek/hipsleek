data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

void append2(node x, node y)
  requires x::ll<n1> * y::ll<n2> & n1>0 // & x!=null // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<m> & m=n1+n2;
@@[-dd -tp z3]
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}


void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null 
  ensures x::ll<n1+n2>;
@@[-tp mona]
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

node ret_first(node x)
	requires x::ll<n> * y::ll<m> & n < m 
	ensures x::ll<n>;

{
	return x;
}
