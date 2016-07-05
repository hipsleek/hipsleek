int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();

	while (x + y > 0)
	case {
		x+y<=0 -> requires Term ensures true;
		x+y>0 -> requires Term[x+y] ensures true;
	}
	{
		int a = rand_int();
		int b = rand_int();
		
		if (a * b > 9) {
			x--;
		} else {
			y--;
		}
	}
}
