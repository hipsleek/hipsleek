void main () 
requires MayLoop
ensures true;
{
	int x = length();
	int y = length();
	loop(x, y);
}

void loop (ref int x, ref int y)
case {
	x<y -> requires Term ensures true;
	x>=y -> case {
		y<0 -> requires Term[x-y] ensures true;
		y>=0 -> requires Loop ensures false;
	}
}
{
	if (x >= y) {
		int z = x - y;
		if (z > 0) {
			x--;
		} else {
			x = 2 * x + 1;
			y++;
		}
		loop(x, y);
	}
}

int length () 
requires Term
ensures res>=0;
