void main ()
requires Term
ensures true;
{
	int i = 0;

	while (true)
	case {
		i>10 -> requires Term ensures true;
		i<=10 -> requires Term[10-i] ensures true;
	}
	{
		if (i > 10) return;
		i++;
	}
}
