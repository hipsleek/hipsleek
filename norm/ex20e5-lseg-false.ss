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

/*
lseg<p> == self = p
	or self::node<_, q> * q::lseg<p> & self != p
  inv true;
*/

lseg2<p> == self = p
	or self::node<_, q> * q::lseg2<p> 
  inv true;

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
   inv k>=0;

HeapPred P(node x,node@NI y).

int len_seg(node x,node p)
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
  infer [P,@classic,@pure_field]
  requires P(x,p)
  ensures false;
{    
  if (x==p) return 0;
  else { 
    node n = x.next;
    // dprint;
    int r=len_seg(n,p);
    //  dprint;
    return 1+r;
  }
}

/*
# ex20e5.ss 

int len_seg(node x,node p)
  infer [P,@classic,@pure_field]
  requires P(x,p)
  ensures false
{    
  if (x==p) return 0;
  else return 1+len_seg(x.next,p);
}

!!! **solver.ml#5511:WARNING : Inferred pure not added: p!=x
Procedure len_seg$node~node SUCCESS.


!!! **solver.ml#5511:WARNING : Inferred pure not added: p!=x
Procedure len_seg$node~node SUCCESS.

Exception(look_up_view_def_raw):Not_found
Exception(get_proot_hp_def_raw):Failure("hp_root_pos has not yet set.")
Exception(Syn.get_root_args_hp):Failure("hp_root_pos has not yet set.")
Exception(Syn.trans_hrel_to_view_formula):Failure("hp_root_pos has not yet set.")
Exception(wrapper_infer_imm_pre_post):Failure("hp_root_pos has not yet set.")

ExceptionFailure("hp_root_pos has not yet set.")Occurred!

Error1(s) detected at main 
Stop z3... 90 invocations 
Stop Omega... 39 invocations caught

Exception occurred: Failure("hp_root_pos has not yet set.")
Error3(s) detected at main 

*/
