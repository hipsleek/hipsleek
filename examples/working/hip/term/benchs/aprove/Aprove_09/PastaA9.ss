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

	if (y > 0) {
		loop(x, y, z);
	}
}

void loop (ref int x, ref int y, ref int z)
case {
	x<z -> requires Term ensures true;
	x>=z -> case {
		y<=0 -> requires Loop ensures false;
		y>0 -> requires Term[x-z] ensures true;
	}
}
{
	if (x >= z) {
		z = z + y;
		loop(x, y, z);
	}
}
