int rand_nat ()
requires Term
ensures res>=0;

void main ()
requires Term
ensures true;
{
	int length = rand_nat();
	int i = 0;
	while (i < length) 
	case {
		i>=length -> requires Term ensures true;
		i<length -> requires Term[length-i] ensures true;
	}
	{
		i++;
	}
}
