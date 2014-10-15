int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	int x = rand_int();
	
	while (x >= 0)
		case {
			x<0 -> requires Term ensures true;
			x>=0 -> requires Term[x] ensures true;
		}
	{
		int y = 1;
		while (x > y)
			case {
				x<=y -> requires Term ensures x'=x;
				x>y -> case {
					y>0 -> requires Term[x-y] ensures x'=x;
					y<=0 -> requires Loop ensures false;
				}
			}
		{
			y = 2 * y;
		}
		x--;
	}
}
