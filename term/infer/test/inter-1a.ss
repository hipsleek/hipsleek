void f (int x)
requires true
ensures true;
{
	if (x<=0) return;
	else g(x);
}

void g (int x)
requires true
ensures true;
{
	if (x<=0) return;
	else f(x-1);
}

