void loop(ref int x, ref int y, ref int z)
case {
	x<y -> ensures "l1":true;
	x>=y -> case {
				z>0 -> //variance x-y
					   ensures "l2":true;
				z=0 -> //
                       ensures "l3":true;
				z=-1 -> //
                        ensures "l4":true;
				z<(-1) -> //variance x-y
					    ensures "l2":true;
			}
}	  
{
	int x1, y1, z1;
	if (x >= y) {
		x1 = x - z;
		y1 = y + z*z;
		z1 = z - 1;
		
		assert "l2":(x1'-y1')-(x'-y')<0;
		assert "l2":(x'-y')>=0;
		//assert "l2":true & ((x1'-y1')>=-10 | z1'=0);  //failed..
		//assert "l2":(x1'-y1')>=-10;  //failed..
		//assert "l5":(x1'-y1')-(x'-y')<0;	
		//assert "l5":(x'-y')>=0;
		//assert "l5":true & ((x1'-y1')>=-10 | z1'=0);  //failed..

		assert "l3":x1'>=y1' & z1'=-1;

		assert "l4":x1'>=y1' & z1'<(-1);
		
		loop(x1, y1, z1);
	}
}
