void test (int n)
case {
	n<=0 -> requires Term[1] ensures true;
	n>0 -> requires Term[n] ensures true;
}
{
	int i = 0;
	
	while (i < n) 
	case {
		i>=n -> requires Term ensures true;
		i<n -> requires Term[n-i] ensures true;
	}
	{
		test(i);
		i++;
	}
}

void main ()
requires Term
ensures true;
{
	test(10);
}
