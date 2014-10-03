void f(int x) {
	x = 1;
}

void g(ref int y)
	requires true
	ensures y'  = 2;
{
	y = 2;
dprint;
	f(y);
dprint;
	assert y'=2;
}
