#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

//C_INCLUDE_PATH=.. ../hip ex5a-a01-loop.c

int test_fun (int* x_ref, int* y_ref, int* c)
/*@
  infer[@shape_prepost]
  requires true
  ensures true;
*/
{
    while (*y_ref < *x_ref) 
      /*@
        infer[@shape_prepost]
        requires true
        ensures true;
      */
      {
            *y_ref = *y_ref + 1;
            *c = *c + 1;
      }
    return *c;
}

int main() 
/*@
  infer[@shape_prepost]
  requires true
  ensures true;
*/
{
  int* x_ref = alloca(sizeof(int));
  int* y_ref = alloca(sizeof(int));
  int* c = alloca(sizeof(int));
  *x_ref = __VERIFIER_nondet_int();
  *y_ref = __VERIFIER_nondet_int();
  *c = __VERIFIER_nondet_int();
  return test_fun(x_ref, y_ref, c);
}

/*
# norm2/ex5a.c

# Need to mark root for unfolding too:

push_list(es_infer_hp_rel):**inferHP.ml#1324:1[ (1;0)unknown HP_1648(c,x_ref,y_ref) |#|  --> x_ref::int_star<value_8_1653>@M * 
                                              HP_1654(c,y_ref,x_ref)]


# Why are there sometimes different copies of programs?

!!! **syn.ml#704:other hprels of GP_1699: 
!!! **cast.ml#3988:Adding the view HP_1654[y_ref,x_ref] into cprog.
!!! **cast.ml#621:prog and cprog are different
**cprog** check_prog_only:false

!!! **WARNING****iast.ml#3922:Updating an available view decl (HP_1654) in iprog
!!! **cast.ml#3988:Adding the view HP_1755[] into cprog.
!!! **cast.ml#621:prog and cprog are different
**cprog** check_prog_only:false

!!! **iast.ml#3923:Adding the view HP_1755 into iprog.
!!! **cast.ml#3988:Adding the view HP_1648[x_ref,y_ref] into cprog.
!!! **cast.ml#621:prog and cprog are different
**cprog** check_prog_only:false

!!! **WARNING****iast.ml#3922:Updating an available view decl (HP_1648) in iprog
!!! **cast.ml#3988:Adding the view HP_1756[x_ref] into cprog.
!!! **cast.ml#621:prog and cprog are different
**cprog** check_prog_only:false

================================================

# PRE_REC seems to have a problem.

[ // BIND
(1;0)HP_1643(c,x_ref,y_ref)&
true --> y_ref::int_star<value_8_1647>@M * HP_1648(c,x_ref,y_ref@NI)&
true,
 // BIND
(1;0)HP_1648(c,x_ref,y_ref@NI)&
true --> x_ref::int_star<value_8_1653>@M * HP_1654(c,y_ref@NI,x_ref@NI)&
true,
 // BIND
(1;1;0)HP_1654(c,y_ref@NI,x_ref@NI)&true --> c::int_star<value_16_1680>@M&
true,
 // PRE_REC
(1;1;0)c'::int_star<v_int_16_1698>@M * GP_1699(x_ref,y_ref',c'@NI)&
true --> HP_1643(c',x_ref,y_ref')&
true,
 // PRE_REC
(1;1;0)y_ref'::int_star<v_int_15_1679>@M * GP_1700(y_ref',x_ref@NI,c'@NI)&
true --> GP_1699(x_ref,y_ref',c'@NI)&
true,
 // PRE_REC
(1;1;0)emp&true |#| x_ref::int_star<value_8_1653>@M&
true --> GP_1700(y_ref',x_ref@NI,c'@NI)&
true]

*/
