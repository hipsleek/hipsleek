void narrowKonv (int i)
case {
	!(0<=i & i<=20) -> requires Term ensures true;
	(0<=i & i<=20) -> requires Loop ensures false;
}
{
	int r = 20;
	loop(i, r);
}

void loop (ref int i, ref int r)
case {
	r<0 -> requires Term ensures true;
	r>=0 -> case {
		!(0<=i & i<=r) -> requires Term ensures true;
		(0<=i & i<=r) -> requires Loop ensures false;	
	}
}
{
	if (0 <= i && i <= r) {
		if (!(0 == i && i == r)) {
			if (i == r) {
				i = 0;
				r--;
			} else {
				i++;
			}
		}
		loop(i, r);
	}
}
