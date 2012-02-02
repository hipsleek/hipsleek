int rand_nat ()
requires Term
ensures res>=0;

void main ()
requires Term
ensures true;
{
	int i = rand_nat();
	int j = rand_nat();
	
	while (i - j >= 1) 
	case {
		i-j<1 -> requires Term ensures true;
		i-j>=1 -> requires Term[i-j] ensures true;
	}
	{
		i = i - rand_nat();
		int r = rand_nat() + 1;
		j = j + r;
	}
}

