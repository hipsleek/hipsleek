int rand_int ()
requires Term
ensures true;

void main () 
requires MayLoop
ensures true;
{
	int x = rand_int();
	int y = rand_int();

	while (x >= y)
	case {
		x<y -> requires Term ensures true;
		x=y -> requires Loop ensures false;
		x>y -> requires Term ensures true;
	}
	{
		int t = x;
		x = y;
		y = t;
	}
}
