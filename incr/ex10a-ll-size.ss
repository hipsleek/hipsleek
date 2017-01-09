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

sll<> == self = null 
	or self::node<_, q> * q::sll<>
  inv true;

HeapPred H(node a).
//HeapPred G(node a, node b).
HeapPred H1(node a).


int size_helper(node x)
  infer[H,@classic]
  requires H(x)  ensures  emp;//H1(x);
{
  if (x==null) 
    return 0;
  else {
    return 1+ size_helper(x.next);
  }
}

/*
# ex10a.ss

  infer[H]
  requires H(x)  ensures  emp;//H1(x);

# Inferred ..

!!! INFERRED SHAPE SPEC:
 EBase 
   x::sll<>@M&{FLOW,(4,5)=__norm#E}[]
   EBase 
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume 
       emp&{FLOW,(4,5)=__norm#E}[]Stop z3... 122 invocations 

 */
