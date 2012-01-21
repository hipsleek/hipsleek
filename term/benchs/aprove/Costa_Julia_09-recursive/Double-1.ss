void test (int n)
case {
	n>0 -> requires Term[n] ensures true;
	n<=0 -> requires Term[1] ensures true;
}
{
	int i = 0;
	loop(i, n);
}

void loop (int i, int n)
requires i>=0
case {
	i>=n -> requires Term ensures true;
	i<n -> requires Term[2*i] ensures true;
}
{
	if (i < n) {
		test(i);
		i++;
		loop(i, n);
	}
}


