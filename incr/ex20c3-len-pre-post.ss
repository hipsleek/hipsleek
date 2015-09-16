/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<> == self = null  
	or self::node<_, q> * q::ll<> 
  inv true;


	
HeapPred P(node x).


int length(node x)
  infer [@shape_pre,@shape_post,@classic]
//  infer [@shape_pre]
//  infer [@shape_pre,@shape_post]
//infer [@shape_pre,@classic]
//infer [@shape_post]
  requires true
  ensures true;
{    
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# ex20c3.ss

  infer [@shape_pre,@shape_post,@classic]
  requires true
  ensures true;

# @shape_pre and @shape_post works separately.
  But not together like here.

!!! INFERRED SHAPE SPEC:
 EInfer @leak[]
   EBase 
     x::ll<>@M&{FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         htrue&{FLOW,(4,5)=__norm#E}[]
         struct:EBase 
                  htrue&{FLOW,(4,5)=__norm#E}[]Stop z3... 108 invocations 


*/
