void f(int x, ref int y)
{
	x = 1;
	y = 2;
}

void g()
{
	int z = 3;
	int w = 4;

	f(z, w);
	assert z'=3;
	assert w'=4;
}

