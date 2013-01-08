int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	
	if (x > 0) {
		while (x > y)
		case {
			x<=y -> requires Term ensures true;
			x>y -> case {
				x>0 -> requires Term[x-y] ensures true;
				x<=0 -> requires Loop ensures false;
			}
		}
		{
			y = x + y;
		}
	}
}
