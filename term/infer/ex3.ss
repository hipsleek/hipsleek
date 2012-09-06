void f(int x)
requires true
ensures true;
{
	if (x<=0) return;
	else return g(x);
}

void g(int y)
requires true
ensures true;
{
	if (y<=0) return;
	else return f(y-1);
}
