void main ()
requires Loop
ensures false;
{
	int j = 100;
	int i = 0;
	while (i < j)
	case {
		i>=j -> requires Term ensures true;
		i<j -> requires Loop ensures false;
	}
	{
		j++;
		i++;
	}
}
