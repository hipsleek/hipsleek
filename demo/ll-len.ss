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
relation R(int a,int b,int c).

int length(node x)
  //infer [R]
  requires x::ll<n> 
    // & x!=null // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<n> & res=n;
{
  if (x == null) return 0;
  else return 1+length(x.next);
}






