int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
		
	while (true)
	case {
		x<0 -> case {
			y<0 -> requires Term ensures true;
			y>=0 -> requires Term[y] ensures true;
		}
		x>=0 -> requires Term[x] ensures true;
	}
	{
		if (x >= 0) {
			x--;
			y = rand_int();
		} else if (y >= 0) {
			y--;
		} else {
			break;
		}
	}
}
