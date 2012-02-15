void main ()
requires Loop
ensures false;
{
	int i = 0;
	while (i < 20)
	case {
		i>=20 -> requires Term ensures true;
		i<20 -> case {
			i>10 -> requires Term[20-i] ensures true;
			i<=10 -> requires Loop ensures false;
		}
	}
	{
		if (i <= 10) { i = i + 0; }
		else i++;
	}
}
