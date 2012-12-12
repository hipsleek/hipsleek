int divBy (int x)
requires Term
ensures true;
{
	int r = 0;
	int y;
	while (x > 0)
	case {
		x<=0 -> requires Term ensures true;
		x>0 -> requires Term[x] ensures true;
	}
	{
		y = 2;
		x = x / y;
		r = r + x;
	}

	return r;
}

int rand_nat ()
requires Term
ensures res>=0;

void main ()
requires Term
ensures true;
{
	int l = rand_nat();
	if (l > 0) {
		int x = l;
		int r = divBy(x);
	}
}
