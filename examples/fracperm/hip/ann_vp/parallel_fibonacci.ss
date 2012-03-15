/*
  Inspired by Fibonacci example in Cilk-5.4.6 Reference Manual
  supertech.csail.mit.edu/cilk/manual-5.4.6.pdf
  Need "-tp z3 -perm none"
  Note: z3 can not handle fractional permission
 */

relation fib(int n, int f) == 
	(n = 0 & f = 1 |
	n = 1 & f = 1 |
	n > 1 & exists(f1, f2 : fib(n-1,f1) & fib(n-2,f2) & f = f1 + f2)).

relation fiba(int n, int f).

  //axiom n=0 ==> fiba(n,1).
  //axiom n=1 ==> fiba(n,1).
axiom 0<=n & n<=1 ==> fiba(n,1).
axiom n > 1 & fiba(n-1,f1) & fiba(n-2,f2) ==> fiba(n,f1+f2).

/* sequential version */
int seq_fib(int n)
	requires n >= 0 & @value[n]
    ensures fiba(n,res);
    //ensures fib(n,res);
{
	if (n < 2)
		return 1;
	else
		return seq_fib(n-1) + seq_fib(n-2);
}

/* sequential version */
void seq_fib2(int n, ref int result)
	requires n >= 0 & @value[n] & @full[result]
    ensures fiba(n,result') & @full[result]; //'
{
	if (n < 2)
		result=1;
	else{
      int result1,result2;
      seq_fib2(n-1,result1);
      seq_fib2(n-2,result2);
      result = result1 + result2;
    }
}

/* parallel version: one child thread */
void para_fib(int n, ref int result)
	requires n >= 0 & @value[n] & @full[result]
    ensures fiba(n,result') & @full[result]; //'
{
	if (n < 2)
		result=1;
	else{
      int result1,result2;
      int id;
      id = fork(para_fib,n-1,result1);
      //any access to result1 and result2 here is not allowed
      para_fib(n-2,result2);
      join(id);
      result = result1 + result2;
    }
}

/* parallel version: two child thread */
void para_fib2(int n, ref int result)
	requires n >= 0 & @value[n] & @full[result]
    ensures fiba(n,result') & @full[result]; //'
{
	if (n < 2)
		result=1;
	else{
      int result1,result2;
      int id1,id2;
      id1 = fork(para_fib2,n-1,result1);
      id2 = fork(para_fib2,n-2,result2);
      //any access to result1 and result2 here is not allowed
      join(id1);
      join(id2);
      result = result1 + result2;
    }
}
