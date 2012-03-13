/********************************************************
Example from "Termination of Polynomial Programs"
Bradley et al. (VMCAI'05)
*********************************************************/

bool rand_bool () 
requires Term
ensures true;

void loop (int x, int y, int z)
requires Term
ensures true;
{
	if (x>=y) {
		bool r = rand_bool();
		if (r) {
			loop_aux_1 (x, y, z);
		} else {
			loop_aux_2 (x, y, z);
		}
	}
}

void loop_aux_1 (int x, int y, int z)
requires x>=y
case {
	x<=1 -> requires Term[1-x] ensures true;
	x>1 -> requires Term[x-y] ensures true;
}
{
	y = y+x;
	x = x+1;
	loop(x, y, z);
}

void loop_aux_2 (int x, int y, int z)
requires x>=y
case {
	z>0 -> requires Term[x-y] ensures true;
	z=0 -> requires Term ensures true;
	z=(-1) -> requires Term ensures true;
	z<(-1) -> requires Term[x-y] ensures true;
}
{
	x = x-z;
	y = y+z*z;
	z = z-1;
	loop(x, y, z);
}
