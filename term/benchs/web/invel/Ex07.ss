void loop (int i)
requires Loop
ensures false;
{
	if (true) {
		if (i > 0) {
			i--;
		}
		if (i < 0) {
			i++;
		}
		loop(i);
	}
}
