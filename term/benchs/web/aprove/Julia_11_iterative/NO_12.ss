void main ()
requires Loop
ensures false;
{
	int j = 0;
	int i = 0;
	while (i <=j)
	case {
		i>j -> requires Term ensures true;
		i<=j -> requires Loop ensures false;
	}
	{
		if (j-i < 1)
			j = j + 2;
		i++;
	}
}
