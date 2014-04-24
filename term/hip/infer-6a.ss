/**************************************
Example from Gulwani et al. PLDI'08
Program analysis as constraint solving
(Used in CAV'08 - Proving Conditional Termination)
**************************************/

void f (ref int x, int y, int n)
requires n>200 & y<9 & Term[]
ensures x'>=200;
{
	x = 0;
	loop(x, y, n);
}

void loop (ref int x, int y, int n)
//infer[x,y,n]
//requires n>200
//requires y>0
/* 
   The following specification has failed to prove
	 precondition with infer[x,y,n]
   Without inference, the termination checker returns that
   1. Term[-x] -> Term[x]: not decreasing
   --> Expectation: infer y>0 
	 2. Term[-x] -> Loop
   --> Expectation: infer n>200
*/

case {
	x>=n -> requires Loop ensures false;
	x<n -> case {
		x+y>=200 -> requires Term[] ensures x'>=200;
		x+y<200 -> requires Term[-x] ensures x'>=200;
	}
}

{
	if (x<n) {
		x = x + y;
		if (x>=200) return;
	}
	loop(x, y, n);
}
