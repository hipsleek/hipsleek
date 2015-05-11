//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int a).
relation Q(int a,int r).

int foo(int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
  infer [P,Q] requires P(a) ensures Q(res,a[5]);
//  infer [@arrvar,P] requires true ensures P(res,a[4]);
{
  if (a[5]>10) {
    return a[5];
  } else {
    assume false;
    return -1;
  }
}

/*
# ex11a2.ss -tp z3 --smtinp

Why did we generate P twice?

WARNING: _0:0_0:0:Z3 error message: 
(error "line 304 column 25: invalid declaration, function 'P' (whith the given signature) already declared")

Checking procedure foo$int[]... 
!!! **wrapper.ml#271:Calling wrap_arr_as_var
WARNING: _0:0_0:0:Z3 error message: 
(error "line 304 column 25: invalid declaration, function 'P' (whith the given signature) already declared")
>>> GENERATED SMT INPUT:

;Variables declarations
(declare-fun a_primed () (Array Int Int))
(declare-fun a () (Array Int Int))
(declare-fun v_int_11_1152_primed () Int)
;Relations declarations
(declare-fun P (Int) Bool)
(declare-fun P (Int) Bool)
;Axioms assertions
;Antecedent
(assert (= a_primed a))
(assert (P (select a 5)))
(assert (= v_int_11_1152_primed 5))
;Negation of Consequence
(assert (not false))
(check-sat)

 */
