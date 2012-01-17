void mirrorInterv (int i)

{
	int range = 20;
	loop(i, range);
}

void loop (ref int i, ref int range)
case {
	
}
{
	if (-range <= i && i <= range) {
		if (range-i < 5 || range+i < 5) {
			i = -i;
		} else {
			range++;
			i--;
			if (i == 0) {
				range = -1;
			}
		}
		loop(i, range);
	}
}
