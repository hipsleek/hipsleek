int rand_int ()
requires Term
ensures true;

bool rand_bool ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	int z = rand_int();

	if (y > 0) {
		while (x < y && y < z)
		//requires y>0
		case {
			x>=y -> requires Term ensures true;
			x<y -> case {
				y>=z -> requires Term ensures true;
				y<z -> case {
					y<=0 -> requires MayLoop ensures true; //Term when (not r)
					y>0 -> requires Term[y-x] ensures true;
				}
			}
		}
		{
			bool r = rand_bool();
			if (r) {
				x = x + y;
			} else {
				z = x - y; // x<y & y>0 -> x-y<=y
			}
		}
	}
}
