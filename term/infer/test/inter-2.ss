void f (int x, int y)
requires true
ensures true;
{
	if (x<=0) return;
	else g(x, y);
}

void g (int x, int y)
requires true
ensures true;
{
	if (x<=0) return;
	else f(x+y, y);
}

