void loop (int i)
case {
	(-5<=i & i<=5) -> requires Loop ensures false;
	!(-5<=i & i<=5) -> requires Term ensures true;
}
{
	if (-5 <= i && i <= 5) {
		if (i > 0) {
			i--;
		}
		if (i < 0) {
			i++;
		}
		loop(i);
	}
}
