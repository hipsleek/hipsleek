void narrowing (int i)
case {
	!(0<=i & i<=20) -> requires Term ensures true;
	(0<=i & i<=20) -> requires Loop ensures false;
}
{
	int r = 20;
	bool up = false;
	loop(i, r, up);
}

void loop (ref int i, ref int r, ref bool up)
case {
	r<0 -> requires Term ensures true;
	r>=0 -> case {
		!(0<=i & i<=r) -> requires Term ensures true;
		(0<=i & i<=r) -> case {
			r=0 -> requires Term ensures true;
			r!=0 -> requires Loop ensures false;
		}
	}
}
{
	if (0 <= i && i <= r) {
		if (i == 0) {
			up = true;
		}
		if (i == r) {
			up = false;
		}
		if (up) {
			i++;
		}
		if (!up) {
			i--;
		}
		if (i == r - 2) {
			r--;
		}
		loop(i, r, up);
	}
}
