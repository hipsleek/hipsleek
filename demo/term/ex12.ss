void loop(ref int x, ref int y, ref int z, bool b)

case {
	x<y -> requires Term ensures "l1":true;
	x>=y -> case {
		b -> case {
			//l4 -> l3 -> l2 -> l1
			x>1 -> requires Term[x-y] // ==> [x<y]
				     ensures "l2":true;
			x=1 -> requires Term ensures "l3":true;
			x<1 -> requires Term[1-x] // ==> [x=1]
				     ensures "l4":true;
		}

		!b -> case {
			//l6 -> l7 -> l5 -> l1
			z>0 -> requires Term[x-y]
				     ensures "l2":true;
			z=0 -> requires Term 
			       ensures "l6":true;
			z=-1 -> requires Term 
			        ensures "l7":true;
			z<(-1) -> requires Term[x-y]
					      ensures "l2":true;
		}
	}
}

/*
l4:x<1
x<1 & D |- var_0 = 1

x<1 & D |- (-x) >= -1

x<1 & D |- (-var_0) - (-x) < 0

D |- D2 * R
------------------------------------------------
D,[-x] |- variance [-var_0] ==> [var_0=1] D2 * R
*/
{
	int x1, y1, z1;
	if (x >= y) {
		//bool b;
		//b = randBool();
		if (b) {
			x1 = x + 1;
			y1 = y + x;
			z1 = z;

			assert "l2":(x1'-y1')-(x'-y')<0;
			assert "l2":(x'-y')>=0;

			assert "l3":x1'>1;

			assert "l4":(-x1')-(-x')<0;
			assert "l4":(-x')>=-1;
			assert "l4":x1'=1; // fails? //'
			
			loop(x1, y1, z1, randBool());
		} else {
			x1 = x - z;
			y1 = y + z*z;
			z1 = z - 1;

			assert "l2":(x1'-y1')-(x'-y')<0;
			assert "l2":(x'-y')>=0;
			//assert "l5":(x1'-y1')-(x'-y')<0;
			//assert "l5":(x'-y')>=0;
			assert "l4":(-x1')-(-x')<0;
			assert "l4":(-x')>=-1;

			assert "l6":z1'=-1;

			assert "l7":z1'<(-1);
		
			
			loop(x1, y1, z1, randBool());
		}
	}
}


bool randBool()
  requires Term
  ensures res or !res;
