/*
  Inspired by Fibonacci example in Cilk-5.4.6 Reference Manual
  supertech.csail.mit.edu/cilk/manual-5.4.6.pdf

  Demonstrate the use of FORK on recursive procedures,
  which is handled in the same way as that of non-recursive
  procedures.

 */

relation fiba(int n, int f).
axiom n=0 ==> fiba(n,0).
axiom n=1 ==> fiba(n,1).
axiom n > 1 & fiba(n-1,f1) & fiba(n-2,f2) ==> fiba(n,f1+f2).

//sequential version
void seq_fib(int n, ref int result)
  requires n >= 0
  ensures fiba(n,result'); //'
{
	if (n <= 1)
      result = n;
	else{
      int result1,result2;
      seq_fib(n-1,result1);
      seq_fib(n-2,result2);
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
    id1 = fork(para_fib,n-1,result1); //FORK a recursive procedure
    id2 = fork(para_fib,n-2,result2); //FORK a recursive procedure

    join(id1);
    join(id2);
    result = result1 + result2;
  }
}
