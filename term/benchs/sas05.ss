/*****************************************************
Example from "Abstraction Refinement for Termination"
Byron Cook et al. (SAS'05)
*****************************************************/

/*
	while (x>=0) {
		x = x+1;
		y = 1;
		while (y<=x) {
			y = y+1;
		}
		x = x-2;
	}
*/

void loop_1 (int x, int y)

case {
	x<0 -> requires Term ensures true;
	x>=0 -> requires Term[x] ensures true;
}

{
	if (x<0)
		return;
	else {
		x = x+1;
		y = 1;
		loop_2(x, y);
		x = x-2;
		loop_1 (x, y);
	}
}

void loop_2 (int x, int y)

case {
	y>x -> requires Term ensures true;
	y<=x -> requires Term[x-y] ensures true;
}

{
	if (y>x)
		return;
	else 
		loop_2 (x, y+1);
}


