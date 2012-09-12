void loop (int x, int y, int z, int t)
requires true
ensures true;
{
	if (x<=0) return;
	else loop(x+y, y+z, z+t, t-1);
}
