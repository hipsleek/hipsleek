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

void main (int x)

requires MayLoop 
ensures true;

{
	bool b = true;
	loop_1 (b);
}

void loop_1 (bool b)

case {
	b -> requires MayLoop ensures true; 
	!b -> requires Term ensures true;
}

{
	if (b) {
		int k = rand_int();
		loop_2 (b, k);
		b = rand_bool();
		loop_1(b);
	}
}

void loop_2 (bool b, int k)

case {
	k<=101 -> requires Term ensures true;
	k>101 -> case {
		b -> requires Term[k] ensures true;
		!b -> requires Loop ensures false;
	}
}

{
	k = k-1;
	if (k>100) {
		if (!b) { k = k+1; }
		loop_2 (b, k);
	}
}
