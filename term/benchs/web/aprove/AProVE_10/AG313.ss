int quot (int x, int y)
requires Term
ensures true;
{
	int i = 0;
	if (x == 0)
		return 0;
	while (x > 0 && y > 0)
	case {
		!(x>0 & y>0) -> requires Term ensures true;
		(x>0 & y>0) -> requires Term[x] ensures true;
	}
	{
		i = i + 1;
		x = (x - 1) - (y - 1);
	}
	return i;
}

int rand_nat ()
requires Term
ensures res>=0;

void main ()
requires Term
ensures true;
{
	int x, y;
	x = rand_nat();
	y = rand_nat() + 1;
	quot(x, y);
}
