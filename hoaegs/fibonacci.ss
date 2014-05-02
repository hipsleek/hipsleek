relation fib(int n, int f) == 
	(n = 0 & f = 1 |
	n = 1 & f = 1 |
	n > 1 & exists(f1, f2 : fib(n-1,f1) & fib(n-2,f2) & f = f1 + f2)).

relation fiba(int n, int f).

  //axiom n=0 ==> fiba(n,1).
  //axiom n=1 ==> fiba(n,1).
axiom 0<=n & n<=1 ==> fiba(n,1).
axiom n > 1 & fiba(n-1,f1) & fiba(n-2,f2) ==> fiba(n,f1+f2).

int computefib(int n)
	requires n >= 0
    ensures fiba(n,res);
    //ensures fib(n,res);
{
	if (n < 2)
		return 1;
	else
		return computefib(n-1) + computefib(n-2);
}
