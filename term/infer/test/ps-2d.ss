void loop (int x)
requires true
ensures true;
{
	if (x<=0) return;
	else {
		loop(x-1);
		if (x<3)
			loop(x+1);
	}
}
