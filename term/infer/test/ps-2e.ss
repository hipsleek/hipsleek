void loop (int x)
requires true
ensures true;
{
	if (x<=0) return;
	else {
		if (x>=3)
			loop(x+1);
		else
			loop(x-1);

		if (x<5)
			loop(x-2);
		else
			loop(x+2);
	}
}
