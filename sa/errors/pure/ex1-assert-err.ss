/* class Error extends __Exc { */
/*   int val; */
/* } */

void __error()
  requires  true
  ensures  true & flow __Error;

relation P(int a).
relation Q(int a).

void f(int n)
//  infer [@flow,@post_n]
/*  case { */
/*   n<3 -> ensures emp & true; */
/*   n>=3 -> ensures emp & true & flow __Error; */
/* } */
  infer [P] requires P(n) ensures true & flow __Error;
//requires true ensures true & flow __norm;
{
  //dprint;
  if (n<3){
    dprint;
    return;
  }
  else {
    n--;
    //  dprint;
    f(n);
    //raise new Error(-1);
     dprint;
     //  assert false;
    __error();
    // dprint;
  }
}

/*

void main() //(int n)
//infer [@flow,@post_n]
  requires true
  ensures true ;
{
  //f(n);
  f(2);
  //f(3);
  //dprint;
}
*/


/*
!!! **typechecker.ml#2010:Dprint:[n]
dprint(simpl): ex1-assert.ss:27: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 )])]

Successful States:
[
 Label: [(,1 ); (,2 )]
 State:emp&exists(P:P(n)) & exists(Q:Q(n')) & n'=n-1 & 3<=n&{FLOW,(4,5)=__norm#E}[]

 ]

assert:ex1-assert.ss:28: 4:  : ok

rel_rhs  Q(n)
inf_rel_ls  ( n'=n & n<=2 & P(n)  Q(n))
rel_rhs  Q(n)
inf_rel_ls  ( n_1439=n & n'=n-1 & Q(n') & P(n) & 3<=n  Q(n))


 */
