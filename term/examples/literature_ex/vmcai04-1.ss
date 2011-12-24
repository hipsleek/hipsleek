/**************************************************************
Example from Podelski and Rybalchenko's VMCAI'04 paper
A complete method for the synthesis of linear ranking functions
***************************************************************/
/* An example of phase-change program */
int loop (int x)
case {
	x < 0 -> variance (0) ensures res < 0;
	x > 5 -> variance (1) ensures res < 0;
	0<=x<=2 -> variance (2) ensures res < 0;
	4<=x<=5 -> variance (3) ensures res < 0;
	2<x<=3 -> variance (4) ensures res < 0;
}

{
	if (x < 0)
		return x;
	else
		return loop (-2*x + 10);
}

/*
Byron Cook et al. (CAV'08)
- Only infers two precondition for termination:
		x > 5 \/ x < 0
- The program always terminates after at MOST 
(not at least) 5 iterations
*/

int loop2 (int x)
case {
	x <= 1 -> variance (0) ensures res <= 1;
	x > 4 -> variance (1) ensures res <= 1;
	x=2 -> variance (2) ensures res <= 1;
	x=4 -> variance (3) ensures res <= 1;
	x=3 -> variance (4) ensures res <= 1;
}

{
	if (x <= 1)
		return x;
	else
		return loop2 (-2*x + 10);
}
