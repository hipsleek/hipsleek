void plait (int i, int j, int k)
requires true
ensures true;
{
	int plaitNext = 0;
	int swap = 0;
	while (i > 0 || j > 0 || k > 0) 
	requires MayLoop
	ensures true;
	{
		if (plaitNext == 0) {
			swap = i;
			i = j/2;
			j = swap*2;
			plaitNext = 1;
		} else {
			swap = k;
			k = j*2;
			j = swap/2;
			plaitNext = 0;
		}
	}
}
