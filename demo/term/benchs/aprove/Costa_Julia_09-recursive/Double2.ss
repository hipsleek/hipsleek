void test (int n)
case {
	n>0 -> requires Term[2*n] ensures true;
	n<=0 -> requires Term[1] ensures true;
}
{
	int i = n - 1;
	while (i >= 0) 
	case {
		i<0 -> requires Term ensures true;
		i>=0 -> requires Term[2*i+1] ensures true;
	}
	{
		test(i);
		i--;
	}
}

void main ()
requires Term
ensures true;
{
	test(10);
}
