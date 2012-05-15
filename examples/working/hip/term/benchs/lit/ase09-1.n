/************************************************************************
Example from "Looper: Lightweight Detection of Infinite Loops at Runtime"
Jacob Burnim et al. (ASE'09)
*************************************************************************/

int rand_int ()
requires Term
ensures true;
/*
void main ()

{
	int x = rand_int();
	int y = rand_int();
	loop(x, y);
}
*/
void loop (ref int x, ref int y)
case {
	(x!=3 & y>0) -> case {
		exists(k0: x=10*k0)   -> requires Loop ensures false;
		exists(k1: x=10*k1+1) -> requires Term ensures true;
		exists(k2: x=10*k2+2) -> requires Loop ensures false;
		exists(k3: x=10*k3+3) -> requires Term ensures true;
		exists(k4: x=10*k4+4) -> requires Loop ensures false;
		exists(k5: x=10*k5+5) -> requires Term ensures true;
		exists(k6: x=10*k6+6) -> requires Loop ensures false;
		exists(k7: x=10*k7+7) -> requires Term ensures true;
		exists(k8: x=10*k8+8) -> requires Loop ensures false;
		exists(k9: x=10*k9+9) -> requires Term ensures true;
	}
	!(x!=3 & y>0) -> requires Term ensures true;
}

{
	if (x != 3 && y > 0) {
		x = (x * x + 2) % 10;
		y = y + 1;
	}
}
