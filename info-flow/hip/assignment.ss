int assign1()
	requires true
	ensures res <^ @Lo;
{
	int x = 1;
	return x;
}

int assign2()
	requires true
	ensures res <^ @Hi;
{
	int x = 1;
	return x;
}

int assign3(int p)
	requires p <^ @Lo
	ensures res <^ @Lo;
{
	int x = p;
	return x;
}

int assign4(int p)
	requires p <^ @Lo
	ensures res <^ @Hi;
{
	int x = p;
	return x;
}

int assign5_fails(int p)
	requires p <^ @Hi
	ensures res <^ @Lo;
{
	int x = p;
	return x;
}

int assign6(int p)
	requires p <^ @Hi
	ensures res <^ @Hi;
{
	int x = p;
	return x;
}
