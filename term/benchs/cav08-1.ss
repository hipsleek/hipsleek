/********************************************************
Example from "Proving Conditional Termination"
Byron Cook et al. (CAV'08)
*********************************************************/

void loop (int x, int y)
case {
	x <= 0 -> requires Term ensures true;
	x > 0 -> case {
		y < 0 -> requires Term[x] ensures true;
		y >= 0 -> requires Loop ensures false;
	}
}
{
	if (x > 0) {
		loop (x+y, y);
	}
}
