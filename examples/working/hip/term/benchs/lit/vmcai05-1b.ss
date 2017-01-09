/********************************************************
Example from "Termination of Polynomial Programs"
Bradley et al. (VMCAI'05)
*********************************************************/

bool rand_bool () 
requires Term
ensures true;

void loop (int x, int y, int z)
requires z<0
case {
	x<y -> requires Term ensures true;
	x>=y -> case {
		z>=(-1) -> requires Term[z+1] ensures true;
		z<(-1) -> requires Term[x-y] ensures true;	
	}
}
{
	if (x>=y) {
		x = x-z;
		y = y+z*z;
		z = z-1;
		loop(x, y, z);
	}
}

