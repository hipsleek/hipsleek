/********************************************************
Example from "Variance Analyses from Invariance Analyses"
Josh Berdine et al. (POPL'07)
*********************************************************/

bool rand_bool () 
requires Term
ensures true;

int rand_int ()
requires Term
ensures true;

void loop (int x, int y, int z)
requires Term[x+y-z]
ensures true; 
{
	bool r;
	if (x+y>z) {
		r = rand_bool();
		if (r) {
			x = x-1;
		} else {
			r = rand_bool();
			if (r) {
				y = y-1;
			} else {
				z = z+1;
			}
		}
		loop(x, y, z);
	}
}
