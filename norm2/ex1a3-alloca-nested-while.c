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
