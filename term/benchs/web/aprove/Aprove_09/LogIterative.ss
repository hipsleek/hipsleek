int log (int x, int y)
requires Term
ensures true;
{
	int r = 0;
	while (x >= y && y > 1)
	case {
		!(x>=y & y>1) -> requires Term ensures true;
		(x>=y & y>1) -> requires Term[x] ensures true;
	}
	{
		r++;
		x = x/y;
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
	int y = rand_int();
	log(x, y);
}
