/*****************************************************
Example from "Termination Proofs for System Code"
Byron Cook et al. (PLDI'06)
*****************************************************/

int Ack (int x, int y)
requires Term[x, y]
ensures true;
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
