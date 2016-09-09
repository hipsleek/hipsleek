//#include <stdlib.h>

//extern int __VERIFIER_nondet_int(void);

// ../hip ex1a-alloca-while.c -infer "@shape_prepost@term"

void loop (int* x, int* y)
/*@
  infer[@shape_prepost,@term]
  requires true
  ensures true;
*/
{
  while (*x > 0) 
    /*@
      infer[@shape_prepost,@term]
      requires true
      ensures true;
    */
    {
    while (*y > 0) 
      /*@
        infer[@shape_prepost,@term]
        requires true
        ensures true;
      */
      {
        *y = *y - 1;
      }
    *x = *x - 1;
  }
}

int main() 
{
  return 0;
}


/*
# ex1a3.c --trace-exc -show-push-list ".*_hp_rel"

# Why such a push? Where did HP_1695(y,x) came from?

push_list(es_infer_hp_rel):1[ (1;1;0)unknown HP_1695(y,x) |#|  --> emp&y=x]

!!! **inferHP.ml#267:args12:[]
!!! **inferHP.ml#281:niu_svl_ni_total:[(x,@NI)]
push_list(es_infer_hp_rel):1[ (1;1;0)unknown HP_1695(y,x) |#|  --> y::int_star<value_21_1712>@M]

(==solver.ml#13547==)
infer_collect_hp_rel#1@21@20
infer_collect_hp_rel#1 inp1 :lhs_node: HP_1695(y,x)
infer_collect_hp_rel#1 inp2 :rhs_node: y'::int_star<value_21_1707>@M
infer_collect_hp_rel#1 inp3 :lhs:
 HP_1695(y,x) * x::int_star<value_14_1694>@M&
v_bool_14_1536' & x'=x & y'=y & v_bool_14_1583' & 0<value_14_1694&
{FLOW,(4,5)=__norm#E}[]
infer_collect_hp_rel#1 inp4 :rhs: y'::int_star<value_21_1707>@M&{FLOW,(4,5)=__norm#E}[]
infer_collect_hp_rel#1 inp5 :es:
  HP_1695(y,x) * x::int_star<value_14_1694>@M&
v_bool_14_1536' & x'=x & y'=y & v_bool_14_1583' & 0<value_14_1694&
{FLOW,(4,5)=__norm#E}[]
 es_infer_hp_rel: [(1;0)unknown HP_1687(x,y) |#|  --> x::int_star<value_14_1694>@M * 
                                                      HP_1695(y,x)]
 es_evars: [value_21_1707]
 es_gen_impl_vars(E): []
 es_infer_obj: [@shape_pre]
 es_evars: [value_21_1707]
 es_cond_path: [1; 1; 0]
 es_var_measures 1: Some(MayLoop[]{})
 es_trace:  SEARCH ==>  InferUnfold  ==>  InferHeap
 es_infer_vars_hp_rel: [HP_1687; HP_1695]
infer_collect_hp_rel#1 inp6 :classic:false
infer_collect_hp_rel#1@21 EXIT:(true,2:  x::int_star<value_14_1694>@M&
v_bool_14_1536' & x'=x & y'=y & v_bool_14_1583' & 0<value_14_1694&
{FLOW,(4,5)=__norm#E}[]
 es_infer_hp_rel: [(1;1;0)unknown HP_1695(y,x) |#|  --> y::int_star<value_21_1712>@M; 
                   (1;0)unknown HP_1687(x,y) |#|  --> x::int_star<value_14_1694>@M * 
                                                      HP_1695(y,x)]
 es_evars: [value_21_1707]
 es_gen_impl_vars(E): []
 es_infer_obj: [@shape_pre]
 es_evars: [value_21_1707]
 es_cond_path: [1; 1; 0]
 es_var_measures 1: Some(MayLoop[]{})
 es_trace:  SEARCH ==>  InferUnfold  ==>  InferHeap
 es_infer_vars_hp_rel: [HP_1687; HP_1695],3:abd heap: y::int_star<value_21_1712>@M,4:None,5:None,6:new rest:None)

===================================

HY is y (or x classified as dangling? 

!!! **syn.ml#183:Merging is not performed due to the set of pre-hprels does not have disjoint conditions:
 
  [(1;1;0)unfold HP_1695(y,x) |#|  --> y::int_star<value_21_1712>@M; 
   (1;1;0)unfold HP_1695(y,x) |#|  --> y::Dangling<>@M&y=x]
WARNING: _0:0_0:0:* between overlapping heaps: ( x::int_star<value_14_1694>@M, y::Dangling<>@M)

WARNING: _0:0_0:0:* between overlapping heaps: ( x::int_star<value_14_1694>@M, y::Dangling<>@M)
Exception(get_proot_hp_def_raw):Failure("hp_root_pos has not yet set.")


[ // BIND
(1;0)HP_1687(x,y)&true --> x::int_star<value_14_1694>@M * HP_1695(y,x@NI)&
true,
 // PRE
(1;1;0)HP_1695(y,x@NI)&true --> y::int_star<value_21_1712>@M&
true,
 // PRE_REC
(1;1;0)y'::int_star<value_21_1722>@M * GP_1745(y',x'@NI)&
y'!=null --> HP_1687(x',y')&
true,
 // PRE_REC
(1;1;0)emp&y'!=null |#| x'::int_star<v_int_30_1744>@M&
true --> GP_1745(y',x'@NI)&
true,
 // PRE
(1;1;0)HP_1695(y,x@NI)&true --> emp&
y=x,
 // PRE_REC
(1;1;0)x'::int_star<v_int_30_1742>@M * GP_1743(y',x'@NI)&
y'=x' & x'!=null --> HP_1687(x',y')&
true,
 // PRE_REC
(1;1;0)emp&x'!=null & y'=x' --> GP_1743(y',x'@NI)&
true]

Procedure while_14_2$int_star~int_star SUCCESS.

Exception(get_proot_hp_def_raw):Failure("hp_root_pos has not yet set.")
Exception(C.get_root_args_hp):Failure("hp_root_pos has not yet set.")


----------------------

Exception(get_proot_hp_def_raw):Failure("hp_root_pos has not yet set.")
Exception(C.get_root_args_hp):Failure("hp_root_pos has not yet set.")

# Why was dangling introduced below?

!!! **syn.ml#183:Merging is not performed due to the set of pre-hprels does not have disjoint conditions:
 
  [(1;1;0)unfold HP_1695(y,x) |#|  --> y::int_star<value_21_1712>@M * 
                                       HP_1713(x,y); 
   (1;1;0)unfold HP_1695(y,x) |#|  --> y::Dangling<>@M&y=x]
WARNING: _0:0_0:0:* between overlapping heaps: ( x::int_star<value_14_1694>@M, y::Dangling<>@M)

WARNING: _0:0_0:0:* between overlapping heaps: ( x::int_star<value_14_1694>@M, y::Dangling<>@M)

=================================

Exception(look_up_view_def_raw):Not_found
Exception(sig_of_formula):Failure("**cfutil.ml#138:Found duplicate star nodes in [ x::int_star<value_14_1694>@M, HP_1713(x,y), y'::int_star<value_21_1723>@M]")
Exception(process_one_match):Failure("**cfutil.ml#138:Found duplicate star nodes in [ x::int_star<value_14_1694>@M, HP_1713(x,y), y'::int_star<value_21_1723>@M]")

=====================================

It seems we need to use IMPLICIT instead EXIST here for
precondition; and maybe also postcondition.

We probably also need to schedule @post to infer
some relations..

 infer[@shape_post GP_1629]requires EXISTS(value_15_1628: y::int_star<value_15_1628>@M&
true&[]requires emp&MayLoop[]
 ensures GP_1629(y)&true{,(4,5)=__norm#E};

!!! **cformula.ml#11406:false ctx removed:
[  hfalse&false&{FLOW,(4,5)=__norm#E}[]
 es_gen_impl_vars(E): []]
!!! **solver.ml#3087:free var to_conseq:y
********************************************
******* shape relational assumptions *******
********************************************
[ // POST
(2;1;0)y::int_star<value_15_1634>@M&true --> GP_1629(y)&
true]
*/
