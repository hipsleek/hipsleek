/*****************************************************
Example from "Termination Proofs for System Code"
Byron Cook et al. (PLDI'06)
*****************************************************/

/*
	do {
		if (z>x) {
			x++;
		} else {
			z++;
		}
	} while (x<y)
*/

void loop (int x, int y, int z)
/*
case {
	x>=y -> requires Term[] ensures true;
	x<y -> case {
		z>x -> requires Term[y-x, y-z] ensures true; //Term[(y-x) + (y-z)] 
		z<=x -> requires Term[x-z] ensures true;
	}
}
*/

case {
	x>=y -> requires Term ensures true;
	x<y -> case {
		y<=z -> requires Term[y-x] ensures true;
		y>z -> requires Term[y-x, y-z] ensures true;
	}
}

{
	if (x>=y)
		return;
	else {
		if (z>x)
			x = x+1;
		else
			z = z+1;
		loop(x, y, z);
	}
}
