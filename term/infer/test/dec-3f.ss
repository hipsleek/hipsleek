void loop(int x, int y, int m, int n)
requires true
ensures true;
{
	if (x==y) return;
	else loop(x-m,y-n,m,n);
}
