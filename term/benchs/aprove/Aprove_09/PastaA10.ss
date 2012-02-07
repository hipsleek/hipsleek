int rand_int ()
requires Term
ensures true;

void main ()
requires Term
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	loop(x, y);
}

void loop (ref int x, ref int y)
case {
	x=y -> requires Term ensures true;
	x>y -> requires Term[x-y] ensures true;
	x<y -> requires Term[y-x] ensures true;
}
{
	if (x != y) {
		if (x > y) {
			y++;
		} else {
			x++;
		}
	}
}
