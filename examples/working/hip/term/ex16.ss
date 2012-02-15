void loop (ref int x, ref int y)
case {
	x < y -> requires Term ensures "l0" : true;
	x = y -> requires Loop ensures false;
	x > y -> case {
					x>1 -> requires Term[x-y]
						   ensures "l1" : true;
					x=1 -> requires Term
					       ensures "l2" : true;
					x<1 -> requires Term[-x]
					       ensures "l3" : true;
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
