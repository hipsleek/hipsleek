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
  while (*x > 0) {
    while (*y > 0) {
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
# ex1a3.ss

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
