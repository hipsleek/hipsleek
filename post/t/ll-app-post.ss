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
  infer [@post_n]
  requires x::ll<n1> * y::ll<n2> 
  & n1>0 
       // & x!=null // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<r> ;
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

/*
# ll-app-post.ss

Post Inference result:
append2$node~node
 requires x::ll<n1> * y::ll<n2> & 1<=n1 & 
MayLoop[]
 ensures x::ll<r_1217> & 0<=n1 & 0<=n2 & n1=r_1217-n2 & n2<r_1217;
*/






