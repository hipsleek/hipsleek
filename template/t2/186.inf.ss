template int r(int x, int y).

//template int r1(int x, int y).
//template int r2(int x, int y).


void loop (int x, int y)
infer [r]

/*
requires Term[r(x, y)]
ensures true;
*/

case {
	x>1 -> requires Term[x] ensures true;
	x=1 -> requires Term[r(x, y) /* x+y, x */] ensures true;
	x=0 -> requires Term[r(x, y) /* x+y, x */] ensures true;
	x<0 -> requires Term[-x] ensures true;
}


/*
infer[r1,r2]
case {
	x>1 -> requires Term[x] ensures true;
	x=1 -> requires Term[r1(x, y)] ensures true;
	x=0 -> requires Term[r2(x, y)] ensures true;
	x<0 -> requires Term[-x] ensures true;
}
*/

{
	if (x > 0) {
		x = x - 1;
		y = y + 1;
		loop(x, y);
	} else {
		if (y > 2) {
			x = x + 1;
			y = y - 2;
			loop(x, y);
		} else
			return;
	}
}
