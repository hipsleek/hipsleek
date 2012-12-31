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
/*
case {
	x<=z -> case {
		y<=z -> requires Term[0] ensures true;
		y>z -> requires Term[0, y-z] ensures true;
	}
	x>z -> requires Term[1, x-z] ensures true;
}
*/

case {
	x<=z -> case {
		y<=z -> requires Term ensures true;
		y>z -> requires Term[y-z] ensures true;
	}
	x>z -> case {
		y<=z -> requires Term[x-z] ensures true;
		y>z -> requires Term[x-z] ensures true;
	}
}

{
	if (x > z || y > z) {
		if (x > z) {
			x--;
		} else if (y > z) {
			y--;
		}
		loop(x, y, z);
	}
}
