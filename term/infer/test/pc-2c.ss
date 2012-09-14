void loop (int x, int y)
requires true
ensures true;
{
	if (x<=0) return;
	else loop(2*x+y, -y+1);
}
