
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


lseg<p> == self = p
  or self::node<_, q> * q::lseg<p> //& self != p
  inv true;

lseg_ss<p,n> == self = p & n=0
  or self::node<_, q> * q::lseg_ss<p,n-1> //& self != p
  inv n>=0;

clist<> == self::node<_,q>*q::lseg<self> ;

lemma_safe self::lseg<p> <- self::lseg<q>*q::node<_,p>.

  n_clist<z> == self::node<_,q>*q::n_lseg<self,z> & self!=z;


n_lseg<p,z> == self = p 
  or self::node<_, q> * q::n_lseg<p,z> & self!=z //& self != p
  inv true;

lemma_safe self::n_lseg<p,z> <- self::n_lseg<q,z>
  *q::node<_,p> & q!=z.

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
   inv k>=0;

HeapPred P(node x,node@NI y).

int len_seg(node x,node p)
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
  requires x::lseg_ss<p,n> & Term[n]
  ensures true;
  requires x::n_clist<p> & Loop
  ensures false;
/*
  requires x::lseg2<p>
  ensures true;
  requires x::ll<>
  ensures true;
*/
{    
  if (x==p) return 0;
  else return 1+len_seg(x.next,p);
}

/*
# ex21d.ss --pred-en-equiv

int len_seg(node x,node p)
  infer [P,@classic,@pure_field]
  requires P(x,p)
  ensures true;
{    
  if (x==p) return 0;
  else return 1+len_seg(x.next,p);
}

!!! **WARNING****solver.ml#9527:do_base_unfold_hp_rel (TBI)Exception(partition_hp_args):Invalid_argument("List.combine")
Exception(look_up_view_def_raw):Not_found

********************************************
******* shape relational assumptions *******
********************************************
[ // POST
(1;0)P(x,p@NI)&p'=p & x'=x & x'=p' --> emp&
true]


ExceptionInvalid_argument("List.combine")Occurred!
!!! **tpdispatcher.ml#2498:xxx rel 
Exception(get_proot_hp_def_raw):Failure("hp_root_pos has not yet set.")
Exception(Syn.find_root_one_hprel):Invalid_argument("List.combine")
Exception(Syn.find_root_hprel):Invalid_argument("List.combine")
Exception(Syn.view_decl_of_hprel):Invalid_argument("List.combine")
Exception(Syn:trans_hprel_to_view):Invalid_argument("List.combine")
Exception(Syn:derive_view):Invalid_argument("List.combine")
Exception(infer_shapes):Invalid_argument("List.combine")
Exception(wrapper_infer_imm_pre_post):Invalid_argument("List.combine")

Error1(s) detected at main 
Stop z3... 87 invocations 
Stop Omega... 47 invocations caught

Exception occurred: Invalid_argument("List.combine")
Error3(s) detected at main 
*/
