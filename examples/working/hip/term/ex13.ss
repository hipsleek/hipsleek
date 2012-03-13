void loop(ref int x, ref int y, ref int z, bool b)
case {
	x<0 -> requires Term ensures "l1":true;
	x>=0 -> case {
		//l2 -> l3 -> l1
		b -> case {
			z>=0 -> requires Term[z]
				    ensures "l2":true;
			z<0 -> requires Term[x]
				   ensures "l3":true;
		}

		//l4 -> l5 -> l1
		!b -> case {
			y>=0 -> requires Term[y]
				    ensures "l4":true;
			y<0 -> requires Term[x]
				   ensures "l5":true;
		}
	}
}
{
	int x1, y1, z1;
	if (x >= 0) {
		//bool b;
		//b = randBool();
		if (b) {
			x1 = x + z;
			y1 = y + 1;
			z1 = z - 2;

			assert "l2": (z1'-z')<0;				//decreasing
			assert "l2": true & (z1'>=0 | z1'<0);	//bounded or changing state

			assert "l3": (x1'-x')< 0;
			//assert "l3": x1'>=0;
			assert "l3": x'>=0;
			
			loop(x1, y1, z1, randBool());
		} else {
			x1 = x + y;
			y1 = y - 2;
			z1 = z;

			assert "l4": (y1'-y')<0;
			assert "l4": true & (y1'>=0 | y1'<0);

			assert "l5": (x1'-x')< 0;
			//assert "l5": x1'>=0;
			assert "l5": x'>=0;
			
			loop(x1, y1, z1, randBool());
		}
	}
}

bool randBool()
  requires Term
  ensures true;
