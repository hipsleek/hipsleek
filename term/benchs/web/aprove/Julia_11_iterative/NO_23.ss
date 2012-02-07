void main ()
requires Loop
ensures false;
{
	int i = 0;
	while (i < 100)
	case {
		i>=100 -> requires Term ensures true;
		i<100 -> requires Loop ensures false;
	}
	{
		if (i < 50) 
			i = 51;
		else
			i = 49;
	}
}
