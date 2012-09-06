void loop (int x)
requires true
ensures true;
{
	if (x<=0) return;
	else loop(10-2*x);
}
