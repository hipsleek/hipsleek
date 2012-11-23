void loop(ref int x, ref int y, ref int z)
case {
	x<y -> ensures "l1":true;
	x>=y -> 
             case {
					//l4 -> l3 -> l2 -> l1
					x>1 -> //variance x-y
						   ensures "l2":true;
					x=1 -> ensures "l3":true;
					x<1 -> //variance -x
						   ensures "l4":true;
				}
			 case {
					//l6 -> l7 -> l5 -> l1
					z>0 -> //variance x-y
						   ensures "l2":true;
					z=0 -> ensures "l6":true;
					z=-1 -> ensures "l7":true;
					z<(-1) -> //variance x-y
							  ensures "l2":true;
				}
}	  
{
	int x1, y1, z1;
	if (x >= y) {
		bool b;
		b = randBool();
		if (b) {
			x1 = x + 1;
			y1 = y + x;
			z1 = z;
            assert "l2": x>1 & (z>0 | z<(-1));
			assert "l2":(x1'-y1')-(x'-y')<0; //failed
			assert "l2":(x-y)>=0;

			assert "l3":x1'>1;

			assert "l4":(-x1')-(-x')<0;
			assert "l4":(-x')>=-1;
        //dprint;
			loop(x1, y1, z1);
		} else {
			x1 = x - z;
			y1 = y + z*z;
			z1 = z - 1;
            assert "l2": x>1 & (z>0 | z<(-1));
			assert "l2":(x1'-y1')-(x'-y')<0; // failed
			assert "l2":(x-y)>=0;
			//assert "l5":(x1'-y1')-(x'-y')<0;
			//assert "l5":(x'-y')>=0;
			assert "l4":(-x1')-(-x')<0; // failed
			assert "l4":(-x')>=-1;

			assert "l6":z1'=-1;

			assert "l7":z1'<(-1);
            //dprint;			
			loop(x1, y1, z1);
		}
	}
}


bool randBool()
  requires true
  ensures true;
