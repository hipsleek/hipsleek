void loop (int x, int y)
requires true
ensures true;
{
	if (x>=5) return;
	else {
		if (x==y) x = 0;
		x = x + 1;
		loop(x, y);
	}
}
