void loop (int i)
requires Loop
ensures false;
{
	if (true) {
		loop(i);
	}
}
