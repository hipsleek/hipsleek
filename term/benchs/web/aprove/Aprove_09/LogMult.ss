int log (int x, int y)
case {
	(x>y & y=1) -> requires Loop ensures false;
	!(x>y & y=1) -> requires Term ensures true;
}
{
	int r = 1;
	if (x < 0 || y < 1)
		return 0;
	else {
		while (x > y)
		requires !(x<0 | y<1)
		case {
			x<=y -> requires Term ensures true;
			x>y -> case { 
				y!=1 -> requires Term[x-y] ensures true;
				y=1 -> requires Loop ensures false;
			}
		}
		{
			y = y * y;
			r = 2 * r;
		}
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
	log(x, 2);
}
