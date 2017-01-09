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
  requires x::ll<n1> * y::ll<n2> //& n1>0 
  ensures x::ll<r> ;
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

/*
# ll-app-post1.ss

  infer [@post_n]
  requires x::ll<n1> * y::ll<n2> //& n1>0 
  ensures x::ll<r> ;

Good to detect pre-condition failure.

Exception Failure("Proving precond failed") Occurred!
(Program not linked with -g, cannot print stack backtrace)

Error(s) detected when checking procedure append2$node~node

However, why did we have Exception below?
Is it due to reverification?



!!! proc.proc_name:append2$node~node
Checking procedure append2$node~node... 
ExceptionNot_foundOccurred!

Error1(s) detected at main 
Stop Omega... 7 invocations caught
(Program not linked with -g, cannot print stack backtrace)

Exception occurred: Not_found
Error3(s) detected at main 


*/






