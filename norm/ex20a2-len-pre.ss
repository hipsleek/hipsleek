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

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
   inv k>=0;

HeapPred P(node x).

int length(node x)
  infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
  requires P(x)
  ensures true;
/*
  requires x::ll<>
  ensures true;
*/
{    
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# ex20a1.ss --pred-en-equiv

# please schedule pred-reuse when below turned on

  ("--pred-en-equiv", Arg.Set Globals.pred_equiv, "attempt to reuse predicates with identical definition");


# compare --ops (old predicate synthesis)

 EInfer @pure_field,@leak[P]
   EBase 
     x::ll<>@M&{FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         htrue&{FLOW,(4,5)=__norm#E}[]
         struct:EBase 
                  htrue&{FLOW,(4,5)=__norm#E}[]Stop z3... 108 invocations 

*/
