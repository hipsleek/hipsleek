void endless (int i)
requires Loop
ensures false;
{
	if (true) {
		i++;
		endless(i);
	}
}
