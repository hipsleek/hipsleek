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

sll<> == self = null 
	or self::node<_, q> * q::sll<>
  inv true;

HeapPred H(node a).
//HeapPred G(node a, node b).
HeapPred H1(node a).


int size_helper(node x)
/*
  infer[H]
  requires H(x)  ensures true;//H1(x);
*/

  infer[@size]
  requires x::sll<>
  ensures x::sll<>;
{
  if (x==null) 
    return 0;
  else {
    return 1+ size_helper(x.next);
  }
}

/*
# ex14c.slk

# This warning can be resolved by making size_1699 implicit or existential.

!!! **imminfer.ml#122:!should_infer_imm_pre:false
Checking procedure size_helper$node... 
!!! **WARNING****solver.ml#4228:FREE VAR IN HEAP RHS :[size_1699]
LHS:  x'::node<Anon_1695,q_1696>@M * q_1696::sll_size<size_1694>@M&
size_1672=size_1694+1 & 0<=size_1694 & !(v_bool_37_1642') & x'!=null & 
x'=x & v_int_40_1640'=1 & v_node_40_1637'=q_1696&{FLOW,(4,5)=__norm#E}[]
RHS:
 EInfer @size[]
   EBase 
     v_node_40_1637'::sll_size<size_1699>@M&{FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         (exists size_1673: v_node_40_1637'::sll_size<size_1673>@M&
         {FLOW,(4,5)=__norm#E}[]
*/
