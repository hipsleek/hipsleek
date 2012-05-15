void loop (ref int x, ref int y)
case {
	x < y -> requires Term ensures "l0" : true;
	x = y -> requires Loop ensures false;
	x > y -> case {
		//exists (n1: n1 < (n1-1)*x + y + n1*(n1-1)/2) -> case {
			y>1 -> requires Term ensures true;
			y=1 -> requires Loop ensures false;
			y<1 -> case {
				x+y=1 -> requires Loop ensures false; // unroll 1 loop
				x+y>1 -> requires Term ensures true;
				x+y<1 -> requires MayLoop ensures true;
			}
		//}
		//!(exists (n2: n2 < (n2-1)*x + y + n2*(n2-1)/2)) -> requires Loop ensures false;
	}
}
{
	int nx, ny;
	if (x > y) {
		nx = x + 1;
		ny = x + y;
		assert "l1": (x'-y')-(nx'-ny')>0;
		loop(nx, ny);
	} else if (x == y) { loop(x,y); }
}
