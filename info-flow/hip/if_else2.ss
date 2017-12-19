int if_rename1(int x, int y)
	requires x <^ @Lo & y <^ @Lo
	ensures res <^ @Lo;
{
	if (x == 0) {
		y = y;
	}
	else {
		y = 0;
	}

	return y;
}

int if_rename2(int x, int y)
	requires x <^ @Lo & y <^ @Lo
	ensures res <^ @Hi;
{
	if (x == 0) {
		y = y;
	}
	else {
		y = 0;
	}

	return y;
}

int if_rename3_fails(int x, int y)
	requires x <^ @Hi & y <^ @Lo
	ensures res <^ @Lo;
{
	if (x == 0) {
		y = y;
	}
	else {
		y = 0;
	}

	return y;
}

int if_rename4(int x, int y)
	requires x <^ @Hi & y <^ @Lo
	ensures res <^ @Hi;
{
	if (x == 0) {
		y = y;
	}
	else {
		y = 0;
	}

	return y;
}

int if_rename5(int x, int y)
	requires x <^ @Lo & y <^ @Hi
	ensures res <^ @Lo;
{
	if (x == 0) {
		y = y;
	}
	else {
		y = 0;
	}

	return y;
}

int if_rename6(int x, int y)
	requires x <^ @Lo & y <^ @Hi
	ensures res <^ @Hi;
{
	if (x == 0) {
		y = y;
	}
	else {
		y = 0;
	}

	return y;
}

int if_rename7_fails(int x, int y)
	requires x <^ @Hi & y <^ @Hi
	ensures res <^ @Lo;
{
	if (x == 0) {
		y = y;
	}
	else {
		y = 0;
	}

	return y;
}

int if_rename8(int x, int y)
	requires x <^ @Hi & y <^ @Hi
	ensures res <^ @Hi;
{
	if (x == 0) {
		y = y;
	}
	else {
		y = 0;
	}

	return y;
}