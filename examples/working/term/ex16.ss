void loop (ref int x, ref int y)
case {
	x < y -> ensures "l0" : true;
	x >= y -> case {
      x>1 -> 
           variance (1) [x-y]
						   ensures "l1" : true;
      x=1 -> variance (2)
					       ensures "l2" : true;
      x<1 -> variance (3) [-x@0]
					       ensures "l3" : true;
			  }
}
{
	int nx, ny;
	if (x >= y) {
		nx = x + 1;
		ny = x + y;
		assert "l1": (x'-y')-(nx'-ny')>0;
		loop(nx, ny);
	}
}
