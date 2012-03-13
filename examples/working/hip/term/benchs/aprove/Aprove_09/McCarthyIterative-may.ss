int mcCarthy (int x)
requires true
ensures true;
{
	int c = 1;
	while (c > 0) 
	requires MayLoop
	ensures true;
	{
		if (x > 100) {
			x = x - 10;
			c--;
		} else {
			x = x + 11;
			c++;
		}
	}
	return x;
}
