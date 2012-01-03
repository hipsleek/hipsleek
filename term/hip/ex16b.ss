void loop (ref int x, ref int y)
case {
  x < y -> variance (0) ensures "l0" : true;
	x = y -> variance (-1) ensures false;
	x > y -> case {
	x>1 ->    variance  [x-y]
						   ensures "l1" : true;
      x=1 -> variance 
					       ensures "l2" : true;
      x<1 -> variance [-x@0]
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
