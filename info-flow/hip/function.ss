int const1()
	requires true
	ensures res <^ @Lo;
{
	return 1;
}

int func_const1()
	requires true
	ensures res <^ @Lo;
{
	return const1();
}

int func_const2()
	requires true
	ensures res <^ @Hi;
{
	return const1();
}


int const2()
	requires true
	ensures res <^ @Hi;
{
	return 1;
}

int func_const3_fails()
	requires true
	ensures res <^ @Lo;
{
	return const2();
}

int func_const4()
	requires true
	ensures res <^ @Hi;
{
	return const2();
}


int id1(int b)
	requires b <^ @Lo
	ensures res <^ @Lo;
{
	return b;
}

int func_id_const1()
	requires true
	ensures res <^ @Lo;
{
	int v = 1;
	return id1(v);
}

int func_id_const2()
	requires true
	ensures res <^ @Hi;
{
	int v = 1;
	return id1(v);
}


int id2(int b)
	requires b <^ @Lo
	ensures res <^ @Hi;
{
	return b;
}

int func_id_const3_fails()
	requires true
	ensures res <^@Lo;
{
	int v = 1;
	return id2(v);
}

int func_id_const4()
	requires true
	ensures res <^ @Hi;
{
	int v = 1;
	return id2(v);
}


int id3_fails(int b)
	requires b <^ @Hi
	ensures res <^ @Lo;
{
	return b;
}

int func_id_const5()
	requires true
	ensures res <^ @Lo;
{
	int v = 1;
	return id3_fails(v);
}

int func_id_const6()
	requires true
	ensures res <^ @Hi;
{
	int v = 1;
	return id3_fails(v);
}


int id4(int b)
	requires b <^ @Hi
	ensures res <^ @Hi;
{
	return b;
}

int func_id_const7_fails()
	requires true
	ensures res <^ @Lo;
{
	int v = 1;
	return id4(v);
}

int func_id_const8()
	requires true
	ensures res <^ @Hi;
{
	int v = 1;
	return id4(v);
}