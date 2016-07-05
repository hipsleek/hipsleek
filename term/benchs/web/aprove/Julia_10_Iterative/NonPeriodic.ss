int rand_int ()
requires Term
ensures true;

void main ()
requires MayLoop
ensures true;
{
	int x = 1, y = 0;

	y = rand_int();

	//AProVE: does not terminate for x = 1 and y = 1
	while (y > 0)
	case {
		y<=0 -> requires Term ensures true;
		y>0 -> requires Loop ensures false;
	}
	{
		if (x > 0)
			x = x - 1;
		else {
			y = y + 1;
			x = y;
		}
	}
}
