/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next#REC;	
}


/* view for a singly linked list */
/*
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;
*/
ll<> == self = null 
	or self::node<_, q> * q::ll<> 
  inv true;

lseg<p> == self = p
	or self::node<_, q> * q::lseg<p> 
  inv true;

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
   inv k>=0;

HeapPred P(node x,node y).

int len_seg(node x,node p)
  infer [P,@classic,@pure_field]
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
  requires P(x,y)
  ensures true;
/*
  requires x::ll<>
  ensures true;
*/
{    
  if (x==p) return 0;
  else return 1+len_seg(x.next,p);
}

/*
# ex21d1.ss --pred-en-equiv

# can we have a better error messafe due to use of y instead of p?

!!! **sa3.ml#3289:DERIVED VIEWS:[]
ExceptionFailure("hp_root_pos has not yet set.")Occurred!

Error1(s) detected at main 
Stop z3... 98 invocations 
Stop Omega... 75 invocations caught

Exception occurred: Failure("hp_root_pos has not yet set.")

*/
