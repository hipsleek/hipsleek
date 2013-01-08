int mod (int x, int y)
requires Term
ensures true;
{
	while (x >= y && y > 0)
	case {
		!(x>=y & y>0) -> requires Term ensures true;
		(x>=y & y>0) -> requires Term[x] ensures true;
	}
	{
		x = minus(x, y);
	}

	return x;
}

int minus (int x, int y)
requires Term
ensures res=x-y;
{
	while (y != 0)
	case {
		y=0 -> requires Term ensures x'=x & y'=y;
		y!=0 -> case {
			y>0 -> requires Term[y] ensures x'=x-y & y'=0;
			y<=0 -> requires Term[-y] ensures x'=x-y & y'=0;
		}
	}
	{
		if (y > 0) {
			y--;
			x--;
		} else {
			y++;
			x++;
		}
	}
	return x;
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
	mod(x, y);
}
