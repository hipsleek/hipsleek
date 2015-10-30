//#include <stdlib.h>

//extern int __VERIFIER_nondet_int(void);

// ../hip ex1a-alloca-while.c -infer "@shape_prepost@term"

void loop (int* x, int* y)
/*@
  infer[@shape_prepost]
  requires true
  ensures true;
*/
{
  while (*x > 0) 
    /*@
      infer[@shape_prepost]
      requires true
      ensures true;
    */
    {
    while (*y > 0) 
      /*@
        infer[@shape_prepost]
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
# ex1a3.c --trace-exc

# WHY is y (or x classified as dangling? 

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
