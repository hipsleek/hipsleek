void test (int n)
case {
	n>1 -> requires Term[2*n] ensures true;
	n<=1 -> requires Term[1] ensures true;
}
{
	loop(n);
}

void loop (int n)
case {
	n>1 -> requires Term[2*n-1] ensures true;
	n<=1 -> requires Term ensures true;
}
{
	n = n - 1;
	if (n > 0) {
		test(n);
		loop(n);
	}
}

void main ()
requires Term
ensures true;
{
	test(10);
}
