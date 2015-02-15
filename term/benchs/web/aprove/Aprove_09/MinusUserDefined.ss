bool gt (int x, int y)
requires Term
case {
	!(x>0 & y>0) -> case {
		x<=0 -> ensures !res;
		x>0 -> ensures res;
	}
	(x>0 & y>0) -> case {
		x>y -> ensures res;
		x<=y -> ensures !res;
	}
}
{
	while (x > 0 && y > 0)
	case {
		!(x>0 & y>0) -> requires Term ensures x'=x & y'=y;
		(x>0 & y>0) -> case {
			x>y -> requires Term[y] ensures x'=x-y & y'=0;
			x<=y -> requires Term[x] ensures x'=0 & y'=y-x;
		}
	}
	{
		x--;
		y--;
	}
	if (x > 0)
		return true;
	else
		return false;
}

int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	int r = 0;
	
	while (gt(x, y)) 
	case {
		x<=0 -> requires Term ensures true;
		x>0 -> case {
			y<0 -> requires Term[x-y] ensures true;
			y>=0 -> case {
				x>y -> requires Term[x-y] ensures true;
				x<=y -> requires Term ensures true;
			}
		}
	}
	{
		y++;
		r++;
	}
}
