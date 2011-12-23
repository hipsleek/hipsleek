/*************************************
Example from Byron Cook's CAV'08 paper
Proving Conditional Termination
**************************************/

void foo (int x, int y)
case {
	x <= 0 -> variance (0) ensures true;
	x > 0 -> case {
		y < 0 -> variance (1) [x] ensures true;
		y >= 0 -> variance (-1) ensures false;
	}
}
{
	if (x > 0) {
		foo(x+y, y);
	}
}



