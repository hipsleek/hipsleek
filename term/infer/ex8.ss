void loop (int x)
requires true
ensures true;
{
	if (x>5 || x<3) return;
	else loop(4-x);
}
