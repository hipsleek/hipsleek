relation sumN (int i, int n, int sum) ==
	(n = 0 & sum = i
	| n > 0 & exists (s : sumN(i, n-1, s) & sum = s + n)).

int sum (int n)

case {
	n<0 -> requires Loop ensures false;
	n>=0 -> requires Term ensures true;
}
/*
case {
	n<0 -> ensures false;
	n>=0 -> ensures sumN(0, n, res);
}
*/
{
	int sum = 0;
	loop(sum, n);
	return sum;
}

void loop (ref int init, ref int n)

case {
	n<0 -> requires Loop ensures false;
	n>=0 -> requires Term[n] ensures true;
}

/*
case {
	n<0 -> ensures false;
	n>=0 -> ensures sumN(init, n, init');
}
*/
{
	if (n != 0) {
		init += n;
		n--;
		loop(init, n);
	}
}
