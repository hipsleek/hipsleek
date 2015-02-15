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
	
	loop_1(x, y, z);
}

void loop_1 (ref int x, ref int y, ref int z)
case {
	x!=y -> requires Term ensures true;
	x=y -> case {
		x>z -> requires Term ensures true;
		x<=z -> requires Term ensures true;
	}
}
{
	if (x == y && x > z) {
		loop_2(x, y, z);
		loop_1(x, y, z); 
	}
}

void loop_2 (ref int x, ref int y, ref int z)
case {
	y>z -> requires Term[y-z] ensures x'<x & y'<=z & z'=z;
	y<=z -> requires Term ensures x'=x & y'<=z & z'=z;
}
{
	if (y > z) {
		x--;
		y--;
		loop_2(x, y, z);
	}
}
