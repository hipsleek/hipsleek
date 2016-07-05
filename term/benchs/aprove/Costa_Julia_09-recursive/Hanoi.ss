void sol (int h, int f, int t, int support) 
case {
	h<=1 -> requires Term ensures true;
	h>1 -> requires Term[h] ensures true;
}
{
	if (h < 1) return;
	else if (h == 1) {
		//System.out.println("from " + from + " to " + to + "\n");
		return;
	} else {
		sol(h - 1, f, support, t);
	  //System.out.println("from " + from + " to " + to + "\n");
	  sol(h - 1, support, t, f);
	}
}

void main ()
requires Term
ensures true;
{
	sol(5, 1, 2, 3);
}
