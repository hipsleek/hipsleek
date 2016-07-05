int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	int z = rand_int();
	
	while (x < y)
	case {
		x>=y -> requires Term ensures true;
		x<y -> case {
			y<=z -> requires Term[y-x] ensures true;
			y>z -> requires Term[y-x, y-z] ensures true; 	
		}
	}
	{
		if (x < z) {
			x++;
		} else {
			z++;
		}
	}
}
