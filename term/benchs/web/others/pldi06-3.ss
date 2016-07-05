/*****************************************************
Example from "Termination Proofs for System Code"
Byron Cook et al. (PLDI'06)
*****************************************************/

void main ()
//main() terminates iff x<0
requires MayLoop
ensures true;

{
	int x, y;
	//assume (x<0);
	if (y>=1) 
		loop(x, y);
}

void loop (int x, int y)

case {
	x<0 -> requires Term ensures true;
	x>=0 -> case {
		y>=0 -> requires Loop ensures false;
		y<0 -> requires Term[x] ensures true;
	}
}

{
	if (x>=0) {
		x = x+y;
		loop(x, y);
	}
}
