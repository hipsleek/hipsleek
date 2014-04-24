/*************************************
Example from Byron Cook's CAV'08 paper
Proving Conditional Termination
**************************************/
//Invalid example

void loop_1 (int x, int y)
case {
	x <= 0 -> requires Term[0] ensures true;
	x > 0 -> case {
		y < 0 -> requires Term[0,-x] ensures true;
		y >= 0 -> requires Loop ensures false;
	}
}
{
	if (x > 0) {
		loop_1 (x+y, y);
	}
}
