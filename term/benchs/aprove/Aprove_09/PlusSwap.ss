void main () 
requires Term
ensures true;
{
	int x, y, r;
	x = rand_int();
	y = rand_int();
	r = 0;

	loop(x, y, r);
	
	r = r + x;
}

void loop (ref int x, ref int y, ref int r)
case {
	y<=0 -> requires Term ensures true;
	y>0 -> case {
		x<=0 -> requires Term ensures true;
		x>0 -> requires Term[x+y] ensures true;
	}
}
{
	if (y > 0) {
		int z = x;
		x = y - 1;
		y = z;
		r++;
		loop(x, y, r);
	}
}

int rand_int () 
requires Term
ensures true;
