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
			y<0 -> requires Term[0] ensures true;
			y>=0 -> requires Term[1,y] ensures true;
		}
		x>=0 -> requires Term[2,x] ensures true;
	}
	{
		if (x >= 0) {
			x--;
			y = rand_int();
		} else if (y >= 0) {
			y--;
		} else {
			return; //Problem with break
		}
	}
}
