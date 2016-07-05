/* sorted lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

ll_b<S> == self = null & S = {}
	or self::node<v, q> * q::ll_b<S1> & S = union(S1, {self});

sll_b<S> == self=null & S={}
	or self::node<v, r> * r::sll_b<S1>  & S=union(S1, {self}) & 
  forall (x: (x notin S1 | v <= (x.val)));

/* Message: error 1: free variables [x.val] in view def sll_b */
