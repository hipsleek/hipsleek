void plait (int i, int j, int k)

{
	int plaitNext = 0;
	loop(i, j, k, plaitNext);
}

void loop (ref int i, ref int j, ref int k, ref int plaitNext)

{
	if (i > 0 || j > 0 || k > 0) {
		int swap = 0;
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
		loop(i, j, k, plaitNext);
	}
}
