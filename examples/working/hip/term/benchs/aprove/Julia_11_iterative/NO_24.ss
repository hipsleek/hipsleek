void main ()
requires Loop 
ensures false;
{
	int a = 1, b = 2;

	while (a + b < 5)
	case {
		a+b>=5 -> requires Term ensures true;
		a+b<5 -> requires Loop ensures false;
	}
	{
		a = a - b;
		b = a + b;
		a = b - a;
	}
}
