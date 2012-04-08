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
	x+y<=0 -> requires Term ensures true;
	x+y>0 -> requires Term[x+y] ensures true;
}
{
	if (x + y > 0) {
		if (x > y) {
			x--;
		} else if (x == y) {
			x--;
		} else {
			y--;
		}
		loop(x, y);
	}
}
