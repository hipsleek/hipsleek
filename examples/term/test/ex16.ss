void loop(ref int x, ref int y, ref int z, bool b)
case {
	x<0 -> ensures "l1":true;
	x>=0 -> case {
				//l2 -> l3 -> l1
				b -> case {
					z>=0 ->	variance (2) [z]
							ensures "l2":true;
					z<0 ->	variance (1) [x]
							ensures "l3":true;
				}

				//l4 -> l5 -> l1
				!b -> case {
					y>=0 -> variance (3) [y]
						    ensures "l4":true;
					y<0 ->	variance (1) [x]
							ensures "l5":true;
				}
		   }
}
{
	int x1, y1, z1;
	if (x >= 0) {
		if (b) {
			x1 = x + z;
			y1 = y + 1;
			z1 = z - 2;

			loop(x1, y1, z1, randBool());
		} else {
			x1 = x + y;
			y1 = y - 2;
			z1 = z;

			loop(x1, y1, z1, randBool());
		}
	}
}

bool randBool()
  requires true
  ensures true;
