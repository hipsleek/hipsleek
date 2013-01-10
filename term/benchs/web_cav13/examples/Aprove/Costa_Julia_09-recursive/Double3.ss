void test (int n)
case {
	n>1 -> requires Term[2*n] ensures true;
	n<=1 -> requires Term[1] ensures true;
}
{
	while (--n > 0)
	case {
		n>1 -> requires Term[2*n-1] ensures true;
		n<=1 -> requires Term ensures true;
	}
	{
		test(n);
	}
}

void main ()
requires Term
ensures true;
{
	test(10);
}
