/*
  Inspired by Fibonacci example in Cilk-5.4.6 Reference Manual
  supertech.csail.mit.edu/cilk/manual-5.4.6.pdf

  Description: calculate Fibonacci numbers in parallel. Use
  Z3 prover for first-order logic constraints.

  Required flag: --en-para --en-thrd-resource -perm none -tp z3
 */

relation fiba(int n, int f).
axiom n=0 ==> fiba(n,0).
axiom n=1 ==> fiba(n,1).
axiom n > 1 & fiba(n-1,f1) & fiba(n-2,f2) ==> fiba(n,f1+f2).

/* sequential version */
void seq_fib(int n, ref int result)
  requires n >= 0
  ensures fiba(n,result');//'
{
	if (n <= 1)
      result = n;
	else{
      int result1,result2;
      seq_fib(n-1,result1);
      seq_fib(n-2,result2);
      //if(result1 == result2) result = 2*result1;
      result = result1 + result2;
    }
}

//parallel version
void para_fib(int n, ref int result)
  requires n >= 0
  ensures fiba(n,result'); //'
{
  if (n < 10){
    seq_fib(n,result);
  }else{
    int result1,result2;
    thrd id1,id2;
    id1 = fork(para_fib,n-1,result1);
    id2 = fork(para_fib,n-2,result2);
    //any access to result1 and result2 here is not allowed
    //if(result1 == result2) result = 2*result1;
    join(id1);
    join(id2);
    result = result1 + result2;
  }
}
