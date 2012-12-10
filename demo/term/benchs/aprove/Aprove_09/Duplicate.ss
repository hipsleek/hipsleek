int round (int x)
case {
	exists (k1: x=2*k1) -> requires Term ensures res=x;
	exists (k2: x=2*k2+1) -> requires Term ensures res=x+1;
}
{
	if (x % 2 == 0)
		return x;
	else
		return x+1;
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

	while (x > y && y > 2)
	case {
		!(x>y & y>2) -> requires Term ensures true;
		(x>y & y>2) -> requires Term[x-y] ensures true;
	}
	{
		x++;
		y = 2 * y;
	}
}
