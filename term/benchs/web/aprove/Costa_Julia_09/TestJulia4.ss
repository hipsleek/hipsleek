void main ()
requires Term
ensures true;
{
	int a;
	int b = 10;
	int length = rand_nat();
	
	if (length > 2)
		a = 3;
	else
		a = -2;

	int i = 0;
	while (i < (a * 5) / b)
	requires (a=3 | a=(-2)) & b=10
	case {
		i>=(5*a)/b -> requires Term ensures a'=a & b'=b;
		i<(5*a)/b -> requires Term[(5*a)/b-i] ensures a'=a & b'=b;
	}
	{
		i++;
	}
}

int rand_nat ()
requires Term
ensures res>=0;
