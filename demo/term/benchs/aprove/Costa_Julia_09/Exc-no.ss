void main ()
requires Term
ensures true;
{
	int i = 0;
	
	while (i < 20)
	case {
		i>=20 -> requires Term ensures true;
		i<20 -> requires Term[20-i] ensures true;
	}
	{
		if (i > 10) { i = i; }
		i = i + 2;
	}
}
