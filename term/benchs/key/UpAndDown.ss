void upAndDown (int i)
case {
	!(0<=i & i<=10) -> requires Term ensures true;
	(0<=i & i<=10) -> requires Loop ensures false;
}
{
	bool up = false;
	loop(up, i);
}

void loop (ref bool up, ref int i)
case {
	!(0<=i & i<=10) -> requires Term ensures true;
	(0<=i & i<=10) -> requires Loop ensures false;
}
{
	if (0 <= i && i <= 10) {
		if (i == 10)
			up = false;
		if (i == 0)
			up = true;
		if (up)
			i++;
		else
			i--;
		loop(up, i);
	}
}
