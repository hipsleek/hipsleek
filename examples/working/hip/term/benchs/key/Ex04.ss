void loop (int i)
requires Loop
ensures false;
{
	if (true) {
		i--;
		loop(i);
	}
}
