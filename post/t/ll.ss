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

	
	
/*ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/





/* append two singly linked lists */

void append2(node x, node y)
  requires x::ll<n1> * y::ll<n2> & n1>0 
       // & x!=null // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2> ;
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}



void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null 
         // n1>0 // & x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2>;
{
    append2(x,y);
}





