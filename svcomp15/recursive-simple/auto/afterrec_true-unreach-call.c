//void __VERIFIER_error()
/*
  requires emp & true
  ensures emp & true & flow __Error;
*/;

/*
pred f_v<n,e> == n<3 & e=0
   or _::f_v<n-1,e1> & n>=3 & e1=0 & e=1
   or _::f_v<n-1,e1> & n>=3 & e1=1 & e=1.
 */
void f(int n)
/*@
  case {
  n<3 -> ensures emp & true;
  n>=3 -> ensures emp & true & flow __Error;
  }
 */
{
  if (n<3)
    // n_0 < 3
    return;
  n--; // [( n_0 < 3 , 0);], [(\neg(n_0 < 3)  /\ n_1 = n_0 -1, 1)]
  f(n); // [( n_0 < 3 , 0);], [(\neg(n_0 < 3)  /\ n_1 = n_0 -1 /\ f(n_1, e_2), 1)]
  // [( n_0 < 3 , 0);(\neg(n_0 < 3)  /\ n_1 = n_0 -1 /\ f(n_1, e_2) /\ e_2 =1 /\ e=1, 1)],
  // [(\neg(n_0 < 3)  /\ n_1 = n_0 -1 /\ f(n_1, e_2) /\ e_2=0, 1)]
  __VERIFIER_error(); // [( n_0 < 3 , 0);], [(\neg(n_0 < 3)  /\ n_1 = n_0 -1 /\ f(n_1, e_2) /\ e_2=0 /\ e=1, 1)]
}

/*
pred main_v<e> == _::f_v<2,e1> & e1=0 & e=0
   or _::f_v<2,e1> & e1=1 & e=1.
 */

void main()
/*@
  requires true
  ensures true;
*/
{
  f(2);
}

/*
checksat _::main_v<e> & e=0.

expect Unsat.
 */
