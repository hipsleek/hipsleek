/*****************************************************
Example from "Termination Proofs for System Code"
Byron Cook et al. (PLDI'06)
*****************************************************/

int Ack (int x, int y)
/*
requires Term[x, y]
ensures true;
*/
case {
	x<=0 -> requires Term ensures true;
	x>0 -> case {
		y>0 -> requires Term[x,y] ensures true;
		y<=0 -> requires Term[x] ensures true;
	}
}
{
	if (x>0) {
		int n;
		if (y>0) {
			y--;
			n = Ack(x, y);
		} else {
			n = 1;
		}
		x--;
		return Ack(x,n);
	} else {
		return y+1;
	}
}
