void loop(int x, int y, int m)
requires true
ensures true;
{
	if (x==y) return;
	else loop(x-m,y-1,m);
}
