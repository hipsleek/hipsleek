/*************************************
Example from Byron Cook's CAV'08 paper
Proving Conditional Termination
**************************************/

// TODO: should detect false follows Loop.

void loop_2 (int x, int y, int z)

case {
	x <= 0 -> requires Term[0] ensures true;
	x > 0 -> case {
		z < 0 -> case {
			y >= 0 -> requires Term[2,y] ensures true;
			y < 0 -> requires Term[1,x] ensures true;
		}
		z > 0 -> case {
			y >= 0 -> requires Loop ensures false;
			y < 0 -> 
            case {
              x+y<=0 -> requires Term[1] ensures true;
              x+y>0 -> case {
                y+z >=0 -> requires Loop ensures false;
                y+z < 0 -> requires /* Term[3,-y]*/ Loop  ensures true;
              }
            }
		}
    //z > 0 -> requires Loop ensures false;
       z = 0 -> 
           case { 
             y<0 -> requires Term[1,x] ensures true;
             y>=0 -> requires Loop ensures false;
	       }
    }
}

{
	if (x <= 0)
		return;
	else
		loop_2 (x+y, y+z, z);
}

/*
Termination checking result:
(17)->(27) (ERR) Term[3; 0 - y]->Loop
 x>0 & z>0 & y<0
         x+y(negative),y+z,z(+ve)
*/
