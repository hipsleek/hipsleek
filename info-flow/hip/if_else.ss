int if_const1(int x)
	requires x <^ @Lo
	ensures res <^ @Lo;
{
	int z;
	if (x == 0) {
		z = 1;
	}
	else {
		z = 0;
	}

	return z;
}

int if_const2(int x)
	requires x <^ @Lo
	ensures res <^ @Hi;
{
	int z;
	if (x == 0) {
		z = 1;
	}
	else {
		z = 0;
	}

	return z;
}

int if_const3_fails(int x)
	requires x <^ @Hi
	ensures res <^ @Lo;
{
	int z;
	if (x == 0) {
		z = 1;
	}
	else {
		z = 0;
	}

	return z;
}

int if_const4(int x)
	requires x <^ @Hi
	ensures res <^ @Hi;
{
	int z;
	if (x == 0) {
		z = 1;
	}
	else {
		z = 0;
	}

	return z;
}


int if_var1(int x, int y)
	requires x <^ @Lo & y <^ @Lo
	ensures res <^ @Lo;
{
	int z;
	if (x == 0) {
		z = y;
	}
	else {
		z = 0;
	}

	return z;
}

int if_var2(int x, int y)
	requires x <^ @Lo & y <^ @Lo
	ensures res <^ @Hi;
{
	int z;
	if (x == 0) {
		z = y;
	}
	else {
		z = 0;
	}

	return z;
}

int if_var3_fails(int x, int y)
	requires x <^ @Hi & y <^ @Lo
	ensures res <^ @Lo;
{
	int z;
	if (x == 0) {
		z = y;
	}
	else {
		z = 0;
	}

	return z;
}

int if_var4(int x, int y)
	requires x <^ @Hi & y <^ @Lo
	ensures res <^ @Hi;
{
	int z;
	if (x == 0) {
		z = y;
	}
	else {
		z = 0;
	}

	return z;
}

int if_var5_fails(int x, int y)
	requires x <^ @Lo & y <^ @Hi
	ensures res <^ @Lo;
{
	int z;
	if (x == 0) {
		z = y;
	}
	else {
		z = 0;
	}

	return z;
}

int if_var5(int x, int y)
	requires x <^ @Lo & y <^ @Hi
	ensures res <^ @Hi;
{
	int z;
	if (x == 0) {
		z = y;
	}
	else {
		z = 0;
	}

	return z;
}

int if_var6(int x, int y)
	requires x <^ @Lo & y <^ @Hi
	ensures res <^ @Hi;
{
	int z;
	if (x == 0) {
		z = y;
	}
	else {
		z = 0;
	}

	return z;
}

int if_var7_fails(int x, int y)
	requires x <^ @Hi & y <^ @Hi
	ensures res <^ @Lo;
{
	int z;
	if (x == 0) {
		z = y;
	}
	else {
		z = 0;
	}

	return z;
}

int if_var8(int x, int y)
	requires x <^ @Hi & y <^ @Hi
	ensures res <^ @Hi;
{
	int z;
	if (x == 0) {
		z = y;
	}
	else {
		z = 0;
	}

	return z;
}
