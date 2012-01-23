int mn (int x, int y)
requires Term
case {
	x<y -> ensures res=x;
	x>=y -> ensures res=y;
}
{
	if (x < y)
		return x;
	else
		return y;
}

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	int r = 0;
	
	while (mn(x-1, y) == y)
	case {
		x-1>=y -> requires Term[x-y] ensures true;
		x-1<y -> requires Term ensures true;
	}
	{
		y++;
		r++;
	}
}

int rand_int ()
requires Term
ensures true;


