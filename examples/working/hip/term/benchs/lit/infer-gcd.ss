/********************************************************
Example from "Proving Conditional Termination"
Byron Cook et al. (CAV'08)
*********************************************************/

int gcd (int x, int y)
/*
requires x>0 & y>0
case {
	x<y -> requires Term[y] ensures true;
	x=y -> requires Term[] ensures true;
	x>y -> requires Term[x] ensures true;
}
*/
requires x>0 & y>0 & Term[x, y]
ensures true;
{
	if (x>y) 
		return gcd (x-y, y);
	else if (x<y)
		return gcd (x, y-x);
	else
		return x;
}
