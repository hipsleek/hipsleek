void main ()
requires Loop
ensures false;
{
	int a = 5;
	int b = 3;
	int i = 0;
	while (i < 10)
	case {
		i>=10 -> requires Term ensures true;
		i<10 -> requires Loop ensures false;
	}
	{
		i = i + 0;
	}

	test(a, b);
}

int test (int a, int b)
requires Term
ensures res = a * b;
{
	return a * b;
}
