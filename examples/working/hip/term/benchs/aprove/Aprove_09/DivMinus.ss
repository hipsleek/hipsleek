int div (int x, int y)
requires Term
ensures true;
{
	int r = 0;
	while (x >= y && y > 0)
	case {
		!(x>=y & y>0) -> requires Term ensures true;
		(x>=y & y>0) -> requires Term[x-y] ensures true;
	}
	{
		x = x - y;
		r = r + 1;
	}
	return r;
}

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	div(x, y);
}

int rand_int ()
requires Term
ensures true;
