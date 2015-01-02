bool eq (int x, int y)
case {
	!(x>0 & y>0) -> requires Term ensures true;
	(x>0 & y>0) -> requires Term[x] ensures true;
}
{
	if (x > 0 && y > 0) {
		return eq(x-1, y-1);
	} else {
		return (x == 0 && y == 0);
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
	eq(x, y);
}
