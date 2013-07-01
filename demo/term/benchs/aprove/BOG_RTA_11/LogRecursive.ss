int log (int x, int y)
case {
	(x>=y & y>1) -> requires Term[x] ensures true;
	!(x>=y & y>1) -> requires Term ensures true;
}
{
	if (x >= y && y > 1) {
		return 1 + log(x/y, y);
	}
	return 0;
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
	log(x, y);
}
