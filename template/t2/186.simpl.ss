template int r1(int x, int y).
template int r2(int x, int y).

template int r(int x, int y). // 3*x + 2*y

void loop (int x, int y)
//infer [r]
//requires Term[r(x, y)]
//ensures true;
infer[r1, r2]
case {
	x > 1 -> requires Term[x] ensures true;
	x = 1 -> case {
		y <= 1 -> requires Term ensures true;
		y > 1 ->
			//requires Term[r(x, y)] ensures true;		
	
			requires Term[r1(x, y)] ensures true;
			//requires Term[2*y-3] ensures true;
			//requires Term[2*y+3] ensures true;
	}
	x = 0 -> case {
		y <= 2 -> requires Term ensures true;
		y > 2 ->
			//requires Term[r(x, y)] ensures true;			

			requires Term[r2(x, y)] ensures true;
			//requires Term[2*y-6] ensures true;
			//requires Term[2*y] ensures true;
	}
	x < 0 -> case {
		y <= 2 -> requires Term ensures true;
		y > 2 -> requires Term[-x] ensures true;
	}
}

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
