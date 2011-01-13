void loop(ref int x, ref int y, ref int z, bool b)
case {
	x<y -> ensures "l1":true;
	x>=y -> case {
				b -> case {
					//l4 -> l3 -> l2 -> l1
					x>1 ->	  variance (1) [x-y]
							  ensures "l2":true;
					x=1 ->	  variance (2)
							  ensures "l3":true;
					x<1 ->	  variance (3) [-x]
						      ensures "l4":true;
				}

				!b -> case {
					//l6 -> l7 -> l5 -> l1
					z>0 ->	  variance (1) [x-y]
							  ensures "l2":true;
					z=0 ->	  variance (5)
							  ensures "l6":true;
					z=-1 ->	  variance (4)
							  ensures "l7":true;
					z<(-1) -> variance (1) [x-y]
							  ensures "l2":true;
				}
			}
}
{
	int x1, y1, z1;
	if (x >= y) {
		if (b) {
			x1 = x + 1;
			y1 = y + x;
			z1 = z;

			loop(x1, y1, z1, randBool());
		} else {
			x1 = x - z;
			y1 = y + z*z;
			z1 = z - 1;

			loop(x1, y1, z1, randBool());
		}
	}
}


bool randBool()
  requires true
  ensures res or !res;
