data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

//todo: proving precondition fails. bug: dont have locs
void append2(node x, node y)
  requires x::ll<n1> * y::ll<n2> //& n1>0
      // & x!=null // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<m> & m=n1+n2;
{    
	if (x.next == null) 
           x.next = y;
    else
           append2(x.next, y);
}
