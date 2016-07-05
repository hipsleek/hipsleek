void main () 
requires Term
ensures true;
{
	int z = length();
	f(z, z);
}

void f (int x, ref int z)
case {
	x<=0 -> requires Term ensures true;
	x>0 -> requires Term[2*x] ensures true;
}
{
	int y = 0;
	if (x > 0) {
		y = 2;
		loop(x, y, z);
	}
}

void loop (int x, int y, ref int z)
requires x>0
case {
	y<=0 -> requires Term ensures true;
	y>0 -> requires Term[2*x-1, y] ensures true;
}
{
	if (y > 0) {
		z = z - 1;
		f(x-y, z);
		y = y - 1;
		loop(x, y, z);
	}
}

int length () 
requires Term
ensures res>=0;
