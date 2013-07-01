void main ()
requires Term
ensures true;
{
	int i = 0;
	while (i < 100)
	case {
		i>=100 -> requires Term ensures true;
		i<100 -> requires Term[100-i] ensures true;
	}
	{
		i++;
	}

	int j = 5;
	while (j < 21)
	case {
		j>=21 -> requires Term ensures true;
		j<21 -> requires Term[21-j] ensures true;
	}
	{
		j = j + 3;
	}
}
