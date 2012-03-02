void fib (int n)
requires n>=0
case {
	n=1 -> requires Term ensures true;
	n<1 -> requires Loop ensures false;
	n>1 -> requires MayLoop ensures true;
}
{
	int i = 0;
	int j = 1;
	loop(i, j, n);
}

void loop (ref int i, ref int j, ref int n)
requires i>=0 & j>=0 & n>=0
case {
	j=n -> requires Term ensures true;
	j!=n -> case {
		j>n -> requires Loop ensures false;
		j<=n -> 
			// The program loops if n is not a Fibonacci number
			// TODO: How to specify this constraints?
			// Can we use relation?
			requires MayLoop ensures true;
	}
}
{
	if (j != n) {
		int t = j + i;
		i = j;
		j = t;
		loop(i, j, n);
	}
}
