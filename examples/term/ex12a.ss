void loop(ref int x, ref int y)
case {
	x<y -> ensures "l1":true;
	x>=y -> case {
				x>1 -> //variance [x-y]
					   ensures "l2":true;
				x=1 -> //variance [] => x>=y & y>1 
                       ensures "l3":true;
				x<1 -> //variance [-x@-1]
					   ensures "l4":true;
			}
}	  
{
	int x1, y1;
	if (x >= y) {
		x1 = x + 1;
		y1 = x + y;
		assert "l2":(x1'-y1')-(x'-y')<0;
		assert "l2":(x-y)>=0;

		assert "l3":x1'>=y1' & x1'>1;

		assert	"l4":(-x1')-(-x')<0;
		assert	"l4":(-x')>=-1;
		
		loop(x1, y1);
	}
}


