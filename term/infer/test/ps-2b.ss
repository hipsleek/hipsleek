void loop (int x)
requires true
ensures true;
{
	if (x<=0) return;
	else {
		loop(x-1);
		if (x<1)
			loop(x+1); // Unreachable branch
		else
			loop(x-1);
	}
}
