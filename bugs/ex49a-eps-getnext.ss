/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


node get_next(node x) 
  requires x::node<_,null>
	ensures res=null;
{
        node t = x.next;
        dprint;
        // x::node<Anon_12,t'>@M&x'=x & t'=null&{FLOW,(4,5)=__norm#E}[]
        assert t'=null;
	return t;
}

/*
# ex49a.ss

# Why is there imm_inference even though there
  isn't any @imm

!!! **imminfer.ml#328:imm infer start
!!! **imminfer.ml#331:imm infer end
!!! **typechecker.ml#4392:imm infer end20

t = bind x to (val_15_1409,next_15_1410) [read] in 
next_15_1410);

# make it implicit var for instantiation?

Checking procedure get_next$node... 
!!! **WARNING****solver.ml#4226:FREE VAR IN HEAP RHS :[val_15_1409',next_15_1410']LHS:
  (exists flted_12_1422: x::node<Anon_12,flted_12_1422>@M&
x'=x & flted_12_1422=null & MayLoop[]&{FLOW,(4,5)=__norm#E}[]

*/

