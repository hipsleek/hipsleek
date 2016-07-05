int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	int z = rand_int();

	loop(x, y, z);
}

void loop (ref int x, ref int y, ref int z)
case {
	x>=y -> requires Term ensures true;
	x<y -> case {
		y<=z -> requires Term[y-x] ensures true;
		y>z -> requires Term[y-x, y-z] ensures true;
	}
}
{
	if (x < y) {
		if (x < z) {
			x++;
		} else {
			z++;
		}
		loop(x, y, z);
	}
}
