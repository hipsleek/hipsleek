void f (int x)
requires true
ensures true;
{
	if (x<=0) return;
	else g(x);
}

void g (int y)
requires true
ensures true;
{
	if (y<=0) return;
	else f(y-1);
}

