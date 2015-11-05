/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next; //#REC;	
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
   infer [
    //P#size
    P,@size
    ,@classic
    ,@pure_field,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
//infer [P#size,@classic,@pure_field]
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
# ex20a1.ss 

We have:

data node {
	int val; 
	node next; //#REC;	
}

Please schedule #REC to be added (as shown in ex20a3.slk)

	node next#REC;	


Otherwise pred_extn fails as below:

!!! **derive.ml#797:aft Typeinfer.update_view:ll_size
!!! **derive.ml#798:new_vd:
 view ll_size<size_prop:int>= 
  EList
    :EBase 
       (* lbl: *){235}->emp&size_prop=0 & self=null&{FLOW,(1,28)=__flow#E}[]
    || :EBase 
          (* lbl: *){236}->(exists Anon_1648,q_1649,
          size_1650: (* lbl: *){236}->self::node<Anon_1648,q_1649>@M * 
                                      q_1649::ll_size<size_1650>@M&
          size_prop=0&{FLOW,(1,28)=__flow#E}[])



# what happen to size_prop=0, should be termination
  base case..

Procedure length: UNKNOWN
 requires x::ll_size<size_prop> & true
 case {
   1<=size_prop -> requires emp & Term[77,1]
                   ensures true & true;
                   
                     
   size_prop<=0 -> requires emp & MayLoop[]
                   ensures true & true;
                   
                     
   }

-----------------------------

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
