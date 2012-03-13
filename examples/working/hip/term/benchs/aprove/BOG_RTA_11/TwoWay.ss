int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	twoWay(true, rand_int());
}

int twoWay (bool terminate, int n) 
case {
	n<0 -> requires Term ensures true;
	n>=0 -> case {
		terminate -> requires Term[n] ensures true;
		!terminate -> requires Loop ensures false;
	}
}
{
	if (n < 0) {
		return 1;
	} else {
		int m = n;
		if (terminate) {
			m--;
		} else {
			m++;
		}
		return m * twoWay(terminate, m);
	}
}

