void loop(ref int x, ref int y)

/*
case {
	x<y -> variance[0] []
	x>=y -> case {
				x>1 -> variance[1] [x-y]
				x=1 -> variance[2] []
				x<1 -> variance[3] [-x]
			}
}

[0] 

[1] x>=y & x>1 |- x1<y1 \/ (x-y)-(x1-y1)>0 & (x-y)>=0 // [1] -> [0] \/ [1]

[2] x1>=y1 & x1>1 \/ x>=y & x=1

[4] x>=y & x=1 \/ x>=y & x<1 & (-x)-(-x1)>0 & (-x)>=0

*/

/*
l4 -> l3 -> l2 -> l1

l4: D = x>=y & x<1 <-> D = x>=y & x<=0
    r = x=0
x=0 & D |- x1>=y1 & x1=1

x=0 or D |- -x>=0

x=0 or D |- (-x1)-(-x)<0

D |- D2 * R
-----------------------------------------------------
D,[-x] |- variance [-x1@0] ==> [x1>=y1 & x1=1] D2 * R

l3: D = x>=y & x=1
    r = true
D |- x1>=y1 & x>=2

D |- D2 * R
--------------------------------------------
D,[] |- variance [] ==> [x>=y & x>=2] D2 * R

l2: D = x>=y & x>1 <-> D = x>=y & x>=2
    r = x-y=0

x-y=0 & D |- x1<y1

x-y=0 or D |- (x-y)<=0

x-y=0 or D |- (x-y)-(x1-y1)<0

D |- D2 * R
------------------------------------------------
D,[x-y] |- variance [x1-y1@0] ==> [x1<y1] D2 * R
*/

case {
	x<y -> ensures "l1":true;
	x>=y -> case {
				x>1 -> //variance [x-y] ==> [x<y]
					   ensures "l2":true;
				x=1 -> //variance [] ==> [x>=y & x>=2] 
                       ensures "l3":true;
				x<1 -> //variance [-x@0] ==> [x>=y & x=1]
					   ensures "l4":true;
			}
}

{
	int x1, y1;
	if (x >= y) {
		x1 = x + 1;
		y1 = x + y;
		//assert "l2":(x1'-y1')-(x'-y')<0;
		//assert "l2":(x-y)>=0;
		//assert "l2":(x1'-y1')>=0; // not needed

		//assert "l3":x1'>=y1' & x1'>1;

		//assert "l4":(-x1')-(-x')<0;
		//assert "l4":(-x')>=-1;
		//assert "l4":(-x)>=0;

		assert "l2": true & (x1'<y1' | x1'>=y1' & x1'>1 & (x'-y')>=0 & ((x1'-y1')-(x-y))<0);

		assert "l3": true & (x1'<y1' | x1'>=y1' & x1'>1 | x1'>=y1' & x1'=1);

		assert "l4": true & (x1'<y1' | x1'>=y1' & x1'>1 | x1'>=y1' & x1'=1 | x1'>=y1' & x1'<1 & -x'>=0 & ((-x')-(-x1'))>0);
		
		loop(x1, y1);
	}
}


