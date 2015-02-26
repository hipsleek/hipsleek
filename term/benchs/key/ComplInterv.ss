void loop (int i)
case {
	(-3<=i & i<=3) -> requires Term ensures true;
	!(-3<=i & i<=3) -> requires Loop ensures false;
}
{
	if (i*i > 9) {
		if (i < 0)
			i = i-1;
		else
			i = i+1;
		loop(i);
	}
}
