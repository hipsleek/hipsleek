void test (int n)
requires Term[1, n*n+1] ensures true;
{
	if (n > 0) {
		test(0);
		loop(1, n);
	}
}

void loop (int i, int n)
requires i>0
case {
	i>=n -> requires Term[0] ensures true;
	i<n -> requires Term[1, n*n-i] ensures true;
}
{
	if (i < n) {
		test(i);
		i++;
		loop(i, n);
	}
}


