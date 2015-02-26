/********************************************************
Example from "Proving Conditional Termination"
Byron Cook et al. (CAV'08)
*********************************************************/
/*
x<=0 \/ x+y<=0 \/ (y<0 /\ x+2*y+z<=0) \/
(y<0 /\ x+3*y+3*z<=0) \/ (y<0 /\ z<=0)
*/

void loop (int x, int y, int z)

case {
	x <= 0 -> requires Term ensures true;
	x > 0 -> case {
		z < 0 -> case {
			y >= 0 -> requires Term[y] ensures true;
			y < 0 -> requires Term[x] ensures true;
		}
		z > 0 -> case {
			y >= 0 -> requires Loop ensures false;
			y < 0 -> case {
				x+y<=0 -> requires Term ensures true;
				x+y>0 -> case {
					y+z >=0 -> requires Loop ensures false;
          y+z < 0 -> requires MayLoop ensures true;
				}
      }
		}
    z = 0 -> case { 
			y<0 -> requires Term[x] ensures true;
			y>=0 -> requires Loop ensures false;
	  }
  }
}

{
	if (x <= 0)
		return;
	else
		loop (x+y, y+z, z);
}

