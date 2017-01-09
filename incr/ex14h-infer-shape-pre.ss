/* singly linked lists */
//../hip ex14-infer-shape-pre-post.ss --classic
/* representation of a node */
data node {
	int val;
	node next;
}

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
  inv k>=0;

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

/*
sll<> == self = null 
	or self::node<_, q> * q::sll<>
  inv true;
*/

HeapPred H(node a).
//HeapPred G(node a, node b).
HeapPred H1(node a).


int size_helper(node x)
/*
  infer[H]
  requires H(x)  ensures true;//H1(x);
*/
  infer[@shape_pre,@classic] 
  requires true 
  ensures htrue;

{
  if (x==null) 
    return 0;
  else {
    return 1+ size_helper(x.next);
  }
}

/*
# ex14h.ss --reverify

# Why did re-verify infer shape again? This
  caused pre-condition to be false!
# I think need to strip of the previous inference commands
  when re-verifying.

!!! INFERRED SHAPE SPEC:
 EInfer @leak,@shape_pre[]
   EBase 
     x::HP_1638<>@M * x::HP_1708<>@M&{FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         htrue&{FLOW,(4,5)=__norm#E}[]
         struct:EBase 
                  htrue&{FLOW,(4,5)=__norm#E}[]
!!! **typechecker.ml#4045:inside reverify:[x]
Checking procedure size_helper$node... 


******************************
******* SPECIFICATION2 ********
******************************
 infer[@leak, @shape_pre ]requires x::HP_1638<>@M * x::HP_1708<>@M&
truerequires emp&MayLoop[]
 ensures htrue&true{,(4,5)=__norm#E};

*/

