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

int length (node xs)
 requires xs::ll<n>
 //variance [n]
 ensures xs::ll<n> & res=n;
 case {
   xs=null ->  //variance [] => false
              ensures res=0;
  xs!=null -> requires xs::ll<n>
 	      //variance [n]
              ensures xs::ll<n> & res=n;
 }
 requires x::ll<n>
 //variance [n]
 case {
   xs=null -> ensures res=0;
   xs!=null -> ensures x::ll<n> & res=n;
 }
{
  if (xs==null) return 0;
  else return 1+length(xs.next);
}




