void upAndDown (int i)
case {
	!(0<=i & i<=10) -> requires Term ensures true;
	(0<=i & i<=10) -> requires Loop ensures false;
}
{
	int up = 0;
	loop(up, i);
}

void loop (ref int up, ref int i)
case {
	!(0<=i & i<=10) -> requires Term ensures true;
	(0<=i & i<=10) -> requires Loop ensures false;
}
{
	if (0 <= i && i <= 10) {
		if (i >= 10)
			up = 0;
		if (i <= 0)
			up = 1;
		if (up >= 1)
			i++;
		else
			i--;
		loop(up, i);
	}
}
