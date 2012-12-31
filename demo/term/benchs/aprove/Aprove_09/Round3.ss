int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	
	while (x % 3 != 0)
	case {
		exists (k0: x=3*k0) -> requires Term ensures true;
		exists (k1: x=3*k1+1) -> requires Term ensures true;
		exists (k2: x=3*k2+2) -> requires Term ensures true;
	}
	{
		x++;
	}
}
