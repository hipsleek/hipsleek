void loop (int x)
requires true
ensures true;
{
	if (x<=0) return;
	else {
		loop(x-1);
		if (x<2)
			loop(x+1);
		else
			loop(x-1);
	}
}
