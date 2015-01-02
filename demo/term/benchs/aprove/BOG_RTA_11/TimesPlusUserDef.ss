int times (int x, int y) 
case {
	y<=0 -> requires Term ensures true;
	y>0 -> requires Term[y] ensures true;
}
{
	if (y == 0)
		return 0;
	if (y > 0)
		return plus(times(x, y - 1), x);
	return 0;
}

int plus (int x, int y)
case {
	y>0 -> 
		case {
			x>0 -> requires Term[y] ensures res=x+y;
			x<=0 -> requires Term[y] ensures res=y;
		}
	y<=0 -> case {
		x>0 -> requires Term[x] ensures res=x;
		x<=0 -> requires Term ensures res=0;
	}
}
{
	if (y > 0) {
		return 1 + plus(x, y-1);
	} else if (x > 0) {
		return 1 + plus(x-1, y);
	} else {
		return 0;
	}
}

int rand_nat ()
requires Term
ensures res>0;

void main ()
requires Term
ensures true;
{
	int x = rand_nat();
	int y = rand_nat();
	times(x, y);
}
