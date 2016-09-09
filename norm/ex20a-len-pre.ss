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

/*
ll<> == self = null 
	or self::node<_, q> * q::ll<> 
  inv true;
*/

HeapPred P(node x).

int length(node x)
/*
  infer [P,@classic,@pure_field]
  requires P(x)
   ensures true;
*/
  requires x::ll<n>
  ensures true;
{    
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# ex20a.ss

Could we schedule:
 shape_derive_view [*].
and then print view (just like ex20c.slk)

If --pred-en-equiv (pred_equiv), we also
need to schedule:
 pred_reuse[*][*].
 pred_reuse_subs[*].

Make Predicate
==============
P(x) == x::node<val_27_1634,next_27_1635>@M * P(next_27_1635) & x!=null
      \/  emp & x=null

--ops  --pred-en-equiv (reuse not working)
*********************************************************
*******relational definition********
*********************************************************
[ P(x_1656) ::= P(next_25_1652) * x_1656::node<val_25_1657,next_25_1652>@M
 or emp&x_1656=null
 (4,5)]
*************************************
!!! INFERRED SHAPE SPEC:
 EInfer @pure_field,@leak[P]
   EBase 
     x::P<>@M&{FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         htrue&{FLOW,(4,5)=__norm#E}[]
         struct:EBase 
                  htrue&{FLOW,(4,5)=__norm#E}[]Stop z3... 96 invocations 

*/
