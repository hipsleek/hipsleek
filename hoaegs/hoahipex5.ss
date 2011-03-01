/**
 Example: array modification.
 **/
/*
relation fact(int n, int m) == (n = 0 & m = 1 | exists (k : fact(n-1,k) & m = k*n)). 
*/
void reduction(ref int n)
	requires n >= 0
	ensures n' = 0;  
{
	int k = n;
	int t = n;
	k = k + 1;
	k = 2 * k;
	k = 4 * k;
	t = t + k;
	t = t + 2 * n;
	n = n + k + t;
	/* if (n > 0) {
		n = n - 1;
		reduction(n);
	} */
}

/* int successor(int n)
	requires true
	ensures res = n + 1;
{
	n = n + 1;
	int m = n + 2;
	n = 2 * m;
	return n;
}

void swap(ref int a, ref int b)
	requires true
	ensures a' = b & b' = a;
{
	int x = a;
	a = b;
	b = x;
}

void swap2(ref int a, ref int b)
	requires true
	ensures a' = b & b' = a;
{
	a = a + b; /* a <- a + b; b <- b */
	b = a - b; /* a <- a + b; b <- a + b - b = a */
	a = a - b; /* a <- a + b - a = b ; b <- a */
} */