void loop(ref int x, ref int y)
case {
  x<y -> ensures "l1":true; //=> {l2,l3,l4}
	x>=y -> case {
				x>1 -> //variance[1] [x-y] => x<y // {1}
					   ensures "l2":true;
				x=1 -> //variance[2] [] => x>1 // {2}
                       ensures "l3":true;
				x<1 -> //variance[3] [-x@-1] => x=1 // {3}
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
		//assert "l2":(x1'-y1')>=0; // not needed

		assert "l3":x1'>=y1' & x1'>1;

		assert	"l4":(-x1')-(-x')<0;
		assert	"l4":(-x')>=-1;
		assert	"l4":(-x)>=0;
		
		loop(x1, y1);
	}
}

/*

l2:
case {
	x<y -> true
	x>=y -> case {
				x>1 -> oldx-oldy>=0 & oldx-oldy - (x-y)>0
				x=1 -> false
				x<1 -> false
			}
}	  

x<y->true & x>=y & x>1 -> (oldx-oldy>=0 & oldx-oldy - (x-y)>0)

not(x<y) & (x>=y & x>1 -> (oldx-oldy>=0 & oldx-oldy - (x-y)>0))

x<y \/ x>=y & x>1 & oldx-oldy>=0 & oldx-oldy - (x-y)>0


l3:
case {
	x<y -> true
	x>=y -> case {
				x>1 -> true
				x=1 -> false
				x<1 -> false
			}
}	  


x<y \/ x>=y & x>1 -> true

l4:
case {
	x<y -> true
	x>=y -> case {
				x>1 -> true
				x=1 -> true
				x<1 -> -oldx>=-1 & -oldx--x>0
			}
}	  


 x>=y & x<1 -> -oldx>=-1 & -oldx--x>0


