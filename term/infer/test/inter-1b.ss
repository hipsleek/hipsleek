void f (int x)
requires true
ensures true;
{
	if (x<=0) return;
	else g(x-1);
}

void g (int x)
requires true
ensures true;
{
	if (x<=0) return;
	else f(x);
}

