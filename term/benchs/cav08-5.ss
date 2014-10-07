/**************************************
Example from 
	"Proving Conditional Termination", Byron Cook et al. (CAV'08)
	"Program analysis as constraint solving", Gulwani et al. (PLDI'08)
**************************************/

void f (ref int x, int y, int n)
requires n>200 & y<9 & MayLoop
ensures x'>=200;
{
	x = 0;
	loop(x, y, n);
}

void loop (ref int x, int y, int n)
case {
	x>=n -> requires Loop ensures false;
	x<n -> case {
		n<=200 -> case {
			y>0 -> case {
				x+y>=200 -> requires Term ensures x'>=200;
				x+y<200 -> case {
					x+y>=n -> requires Loop ensures false;
					x+y<n -> requires MayLoop ensures true;
				}
			}
			y<=0 -> requires Loop ensures false;
		}
		n>200 -> case {
			x<200 -> case {
				//When x>=200, loop terminates immediately
				y>0 -> requires Term[200-x] ensures x'>=200;
				y<=0 -> requires Loop ensures false;
			}
			x>=200 -> case {
				y>=0 -> requires Term ensures true;
				y<0 -> case {
					x+y>=200 -> requires Term ensures x'>=200;
					x+y<200 -> requires Loop ensures false;
				}
			}
		}
	}
}

{
	if (x<n) {
		x = x + y;
		if (x>=200) return;
	}
	loop(x, y, n);
}
