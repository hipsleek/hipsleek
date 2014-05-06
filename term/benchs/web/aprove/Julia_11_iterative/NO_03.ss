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
		int j = 0;
		while (j < 1)
		case {
			j>=1 -> requires Term ensures true;
			j<1 -> requires Term[1-j] ensures false;
		}
		{
			j = j + 1;
		}
		i = i + 0;
	}
}
