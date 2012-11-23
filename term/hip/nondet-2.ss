bool rand_bool () 
requires Term
ensures true;

void loop (int x, int y)
case {
	x>=0 & y>=0 -> requires MayLoop ensures true;
	!(x>=0 & y>=0) -> requires Term ensures true;
}
{
	if (x>=0 && y>=0) {
		bool r = rand_bool();
		if (r) {
			x = x-1;
			y = y+1;
		} else {
			x = x+1;
			y = y-1;
		}
		loop(x, y);
	}
}

