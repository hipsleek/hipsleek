bool binary1(int x, int y)
	requires x <^ @Lo & y <^ @Lo
	ensures res <^ @Lo;
{
	return (x == y);
}

bool binary2_fails(int x, int y)
	requires x <^ @Lo & y <^ @Hi
	ensures res <^ @Lo;
{
	return (x == y);
}

bool binary3_fails(int x, int y)
	requires x <^ @Hi & y <^ @Lo
	ensures res <^ @Lo;
{
	return (x == y);
}

bool binary4_fails(int x, int y)
	requires x <^ @Hi & y <^ @Hi
	ensures res <^ @Lo;
{
	return (x == y);
}

bool binary5(int x, int y)
	requires x <^ @Lo & y <^ @Lo
	ensures res <^ @Hi;
{
	return (x == y);
}

bool binary6(int x, int y)
	requires x <^ @Lo & y <^ @Hi
	ensures res <^ @Hi;
{
	return (x == y);
}

bool binary7(int x, int y)
	requires x <^ @Hi & y <^ @Lo
	ensures res <^ @Hi;
{
	return (x == y);
}

bool binary8(int x, int y)
	requires x <^ @Hi & y <^ @Hi
	ensures res <^ @Hi;
{
	return (x == y);
}