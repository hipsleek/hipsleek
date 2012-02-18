/*****************************************************
Example from "Termination Proofs for System Code"
Byron Cook et al. (PLDI'06)
*****************************************************/

bool rand_bool () 
requires Term
ensures true;

int rand_int ()
requires Term
ensures true;

void main () 
requires MayLoop
ensures true;
{
	int x = rand_int();
	int y = rand_int();
	int z = rand_int();
	if (y>0)
		loop(x, y, z);
}

void loop (int x, int y, int z)
case {
	((x<0 & y<z) | (x<y & 2*y<z)) ->
		requires MayLoop ensures true;
	!((x<0 & y<z) | (x<y & 2*y<z)) -> 
		requires Term ensures true;
}
{
	bool b = rand_bool();
	if (b)
		x = x+y;
	else
		z = z-y;
	if (x<y && y<z) 
		loop_aux (x, y, z);
}

void loop_aux (int x, int y, int z)
case {
	(x<y & y<z) -> case {
		y>0 -> requires Term[y-x,z] ensures true;
		y<=0 -> requires Loop ensures false;
	}
	!(x<y & y<z) -> requires Term ensures true;
}
{
	if (x<y && y<z) {
		bool b = rand_bool();
		if (b) 
			x = x+y;
		else
			z = z-y;
		loop_aux(x, y, z);
	}
}
