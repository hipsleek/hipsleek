void test (int n)
requires Term[1, n*n+1] ensures true;
{
	if (n > 0) {
		test(0);
		int i = 1;
		while (i < n) 
		requires i>0
		case {
			i>=n -> requires Term[0] ensures true;
			i<n -> requires Term[1, n*n-i] ensures true;
		}
		{
			test(i);
			i++;
		}
	}
}

void main ()
requires Term
ensures true;
{
	test(10);
}
