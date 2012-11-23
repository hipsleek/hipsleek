relation fib(int n, int f) == 
	(n = 0 & f = 1 |
	n = 1 & f = 1 |
	n > 1 & exists(f1, f2 : fib(n-1,f1) & fib(n-2,f2) & f = f1 + f2)).

relation fiba(int n, int f).

axiom true ==> fiba(0,1) & fiba(1,1).
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

int fibwhile(int n) 
	requires n >= 0
	ensures fiba(n,res);
	//ensures fib(n,res);
{
  int r1 = 1;
  int r2 = 1;
  assume fiba(0,1) & fiba(1,1);
  while (n>0)
    requires [m] fiba(m,r1) & fiba(m+1,r2) & n>=0
    ensures fiba(m+n,r1') & fiba(m+n+1,r2') & n'=0;//'
    {
      int t = r1+r2;
      r1 = r2;
      r2 = t;
      n=n-1;
    }
  return r1;
}

/*

int fibwhile1(int n) 
	requires n >= 0
	ensures fiba(n,res);
	//ensures fib(n,res);
{
	assume fiba(0,1) & fiba(1,1);
	return fibwhilehelper1(n,1,1);
}

int fibwhilehelper1(int n, int f0, int f1) 
	requires [m] fiba(m,f0) & fiba(m+1,f1) & n >= 0 & m >= 0
	ensures fiba(m+n,res);
	//requires fib(m,f0) & fib(m+1,f1) & n >= 0 & m >= 0
	//ensures fib(m+n,res);
{
	if (n == 0)
		return f0;
	else if (n == 1)
		return f1;
    else
		return fibwhilehelper1(n-1,f1,f0+f1);
}
*/
