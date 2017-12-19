int rec1a()
	requires true
	ensures res <^ @Lo;
{
	return rec1b();
}

int rec1b()
	requires true
	ensures res <^ @Hi;
{
	return rec1a();
}


int rec2a(int x)
	requires x <^ @Lo
	ensures res <^ @Lo;
{
	return rec2a(x);
}

int rec2b(int x)
	requires x <^ @Lo
	ensures res <^ @Hi;
{
	return rec2b(x);
}

int rec2c(int x)
	requires x <^ @Hi
	ensures res <^ @Lo;
{
	return rec2c(x);
}

int rec2d(int x)
	requires x <^ @Hi
	ensures res <^ @Hi;
{
	return rec2d(x);
}