int log (int x)
requires Term
ensures true;
{
	int r = 0;
	while (x > 1)
	case {
		x<=1 -> requires Term ensures true;
		x>1 -> requires Term[x] ensures true;
	}
	{
		x = x/2;
		r++;
	}
	return r;
}

int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	log(x);
}
