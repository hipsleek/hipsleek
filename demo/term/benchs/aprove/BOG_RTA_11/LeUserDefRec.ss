bool le (int x, int y)
case {
	(x>0 & y>0) -> case {
		x>y -> requires Term[y] ensures !res;
		x<=y -> requires Term[x] ensures res;
	}
	!(x>0 & y>0) -> requires Term 
	case {
		x=0 -> ensures res;
		x!=0 -> ensures !res;
	}
}
{
	if (x > 0 && y > 0)
		return le(x-1, y-1);
	else
		return (x == 0);
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
	le(x, y);
}
