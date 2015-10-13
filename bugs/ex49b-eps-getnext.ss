/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


node get_next(node x) 
  requires x::node<_,_>
	ensures res=null;
{
        node t = x.next;
        dprint;
        // x::node<Anon_12,t'>@M&x'=x & t'=null&{FLOW,(4,5)=__norm#E}[]
        assert t'=null;
	return t;
}

// expects failure..

/*

# ex49a.ss (FIXED by making implicit inst for bind)



t = bind x to (val_15_1409,next_15_1410) [read] in 
next_15_1410);

# make it implicit var for instantiation?

Checking procedure get_next$node... 
!!! **WARNING****solver.ml#4226:FREE VAR IN HEAP RHS :[val_15_1409',next_15_1410']LHS:
  (exists flted_12_1422: x::node<Anon_12,flted_12_1422>@M&
x'=x & flted_12_1422=null & MayLoop[]&{FLOW,(4,5)=__norm#E}[]

(==typechecker.ml#1990==)
heap_entail_struc_list_failesc_context_init#5@1
heap_entail_struc_list_failesc_context_init#5 inp1 : List of Failesc Context: [FEC(0, 0, 1  [])]
 Successful States:
 [State:  (exists flted_12_1422: x::node<Anon_12,flted_12_1422>@M&
x'=x & flted_12_1422=null & MayLoop[]&{FLOW,(4,5)=__norm#E}[]]
heap_entail_struc_list_failesc_context_init#5 inp2 : EBase 
   x'::node<val_15_1409',next_15_1410'>@L&{FLOW,(1,28)=__flow#E}[]
heap_entail_struc_list_failesc_context_init#5@1 EXIT: List of Failesc Context: [FEC(1, 0, 0 )]

*/

