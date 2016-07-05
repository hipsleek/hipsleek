/********************************************************
Example from "Termination of Polynomial Programs"
Bradley et al. (VMCAI'05)
*********************************************************/

bool rand_bool () 
requires Term
ensures true;

void loop (int x, int y, int z)
case {
	x<y -> requires Term ensures true;
	x>=y -> case {
		x<=1 -> requires Term[1-x] ensures true;
		x>1 -> requires Term[x-y] ensures true;
	}
}
{
	if (x>=y) {
		y = y+x;
		x = x+1;
		loop(x, y, z);
	}
}

