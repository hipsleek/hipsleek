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
	rec(x, y, z);
}

void rec(int x, int y, int z) 
case {
	x+y+3*z<0 -> requires Term ensures true;
	x+y+3*z>=0 -> requires Term[x+y+3*z] ensures true;
}
{
	if (x + y + 3 * z < 0)
		return;
	else if (x > y)
		rec(x - 1, y, z);
	else if (y > z)
		rec (x, y - 2, z);
	else
	  rec (x, y, z - 1);
}


