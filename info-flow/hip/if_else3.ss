int if_else_const1(int x)
	requires x <^ @Lo
	ensures res <^ @Lo;
{
	int z = 0;
	if (x == 0) {
		z = 1;
	}
	else {
		z = 2;
	}

	return z;
}

int if_else_const2(int x)
	requires x <^ @Lo
	ensures res <^ @Hi;
{
	int z = 0;
	if (x == 0) {
		z = 1;
	}
	else {
		z = 2;
	}

	return z;
}

int if_else_const3_fails(int x)
	requires x <^ @Hi
	ensures res <^ @Lo;
{
	int z = 0;
	if (x == 0) {
		z = 1;
	}
	else {
		z = 2;
	}

	return z;
}

int if_else_const4(int x)
	requires x <^ @Hi
	ensures res <^ @Hi;
{
	int z = 0;
	if (x == 0) {
		z = 1;
	}
	else {
		z = 2;
	}

	return z;
}


int if_else_var1(int x, int y, int z)
	requires x <^ @Lo & y <^ @Lo & z <^ @Lo
	ensures res <^ @Lo;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var2(int x, int y, int z)
	requires x <^ @Lo & y <^ @Lo & z <^ @Lo
	ensures res <^ @Hi;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var3_fails(int x, int y, int z)
	requires x <^ @Lo & y <^ @Lo & z <^ @Hi
	ensures res <^ @Lo;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var4(int x, int y, int z)
	requires x <^ @Lo & y <^ @Lo & z <^ @Hi
	ensures res <^ @Hi;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var5_fails(int x, int y, int z)
	requires x <^ @Lo & y <^ @Hi & z <^ @Lo
	ensures res <^ @Lo;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var6(int x, int y, int z)
	requires x <^ @Lo & y <^ @Lo & z <^ @Lo
	ensures res <^ @Hi;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var7_fails(int x, int y, int z)
	requires x <^ @Lo & y <^ @Hi & z <^ @Hi
	ensures res <^ @Lo;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var8(int x, int y, int z)
	requires x <^ @Lo & y <^ @Hi & z <^ @Hi
	ensures res <^ @Hi;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var9_fails(int x, int y, int z)
	requires x <^ @Hi & y <^ @Lo & z <^ @Lo
	ensures res <^ @Lo;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var10(int x, int y, int z)
	requires x <^ @Hi & y <^ @Lo & z <^ @Lo
	ensures res <^ @Hi;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var11_fails(int x, int y, int z)
	requires x <^ @Hi & y <^ @Lo & z <^ @Hi
	ensures res <^ @Lo;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var12(int x, int y, int z)
	requires x <^ @Hi & y <^ @Lo & z <^ @Hi
	ensures res <^ @Hi;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var13_fails(int x, int y, int z)
	requires x <^ @Hi & y <^ @Hi & z <^ @Lo
	ensures res <^ @Lo;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var14(int x, int y, int z)
	requires x <^ @Hi & y <^ @Hi & z <^ @Lo
	ensures res <^ @Hi;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var15_fails(int x, int y, int z)
	requires x <^ @Hi & y <^ @Hi & z <^ @Hi
	ensures res <^ @Lo;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}

int if_else_var16(int x, int y, int z)
	requires x <^ @Hi & y <^ @Hi & z <^ @Hi
	ensures res <^ @Hi;
{
	int w = 0;
	if (x == 0) {
		w = y;
	}
	else {
		w = z;
	}

	return w;
}