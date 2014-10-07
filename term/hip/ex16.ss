void loop (ref int x, ref int y)
case {
	x < y -> variance [0,0] ensures "l0" : true;
	x = y -> variance [0,-1] ensures false;
	x > y -> case {
					x>1 -> variance [0,1,x-y]
						   ensures "l1" : true;
					x=1 -> variance [0,2,0]
					       ensures "l2" : true;
					x<1 -> variance [0,3,-x]
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
