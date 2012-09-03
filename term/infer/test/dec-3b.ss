void loop(int x, int y)
requires true
ensures true;
{
	if (x==y) return;
	else loop(x-2,y-1);
}
