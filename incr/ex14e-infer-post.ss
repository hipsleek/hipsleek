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
  infer[//@post_n
  ] 
  requires x::ll<a>
  ensures (exists b: x::ll<b>);
{
  if (x==null) 
    return 0;
  else {
    return 1+ size_helper(x.next);
  }
}

/*
# ex14e.slk --pcp

       EAssume 
         (exists b_71: x::ll<b_71>@M&{FLOW,(4,5)=__norm#E}[])
         struct:EBase 
                  (exists b_70: x::ll<b_70>@M&{FLOW,(4,5)=__norm#E}[])

static  EInfer []
   EBase 
     exists (Expl)[](Impl)[a](ex)[]x::ll<a>@M&{FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         (exists b_71: x::ll<b_71>@M&{FLOW,(4,5)=__norm#E}[]
dynamic  EBase 
   hfalse&false&{FLOW,(4,5)=__norm#E}[]

# EBase does not capture existential var !
   EBase 
     (exists a_72: x::ll<a_72>@M&{FLOW,(4,5)=__norm#E}[])

# (exists b: in post seems to have disappeared and became implicit later ..

id: 15; caller: []; line: 36; classic: false; kind: POST; hec_num: 1; evars: []; infer_vars: [ ]; c_heap: emp; others: [] globals: [@flow,@ver_post]
 checkentail x::ll<a>@M&
v_bool_38_1647' & x'=null & x'=x & v_int_39_1638'=0 & res=v_int_39_1638' & 
MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  (exists : x::ll<b_71>@M&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
    emp&
v_bool_38_1647' & x'=null & x'=x & v_int_39_1638'=0 & res=v_int_39_1638' & 
b_71=a&{FLOW,(4,5)=__norm#E}[]
   ]

---------------------------------------------

# Why is there a free_var warning; and how did it manage
  to prove it. Is that still treated as implicit?

!!! **WARNING****solver.ml#4228:FREE VAR IN HEAP RHS :[b_71]
LHS:
  x::ll<a>@M&
v_bool_37_1647' & x'=null & x'=x & v_int_38_1638'=0 & res=v_int_38_1638'&
{FLOW,(4,5)=__norm#E}[]
RHS:
 EBase 
   (exists : x::ll<b_71>@M&post_1653(b_71,a,res,flow)&{FLOW,(4,5)=__norm#E}[]

==================================

Post Inference result:
size_helper$node
 EBase 
   exists (Expl)[](Impl)[a](ex)[]x::ll<a>@M&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists b_71: x::ll<b_71>@M&res>=0 & res=b_71 & res=a&
     {FLOW,(4,5)=__norm#E}[]

*/
