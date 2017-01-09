/********************************************************
Example from 
	"Proving Conditional Termination", Byron Cook et al. (CAV'08)
	"The polyranking principle", Bradley et al. (ICALP'05)
*********************************************************/

bool rand_bool () 
requires Term
ensures true;

void loop (int x, int y, int N)
case {
	x>N -> requires Term ensures true;
	x<=N -> case {
	  x+y<=(-1) -> requires MayLoop ensures true;
		x+y=0 -> requires Term ensures true;
		x+y>0 -> requires Term[N-x] ensures true;
	}
}
{
	if (x<=N) {
		bool r = rand_bool();
		if (r) {
			x = 2*x + y;
			y++;
		} else {
			x++;
		}
		loop(x, y, N);
	}
}
