int const_lo()
	requires true
	ensures res <^ @Lo;
{
	return 1;
}

int const_hi()
	requires true
	ensures res <^ @Hi;
{
	return 1;
}

int const_lolo(int p)
	requires p <^ @Lo
	ensures res <^ @Lo;
{
	return 1;
}

int const_lohi(int p)
	requires p <^ @Lo
	ensures res <^ @Hi;
{
	return 1;
}

int const_hilo(int p)
	requires p <^ @Hi
	ensures res <^ @Lo;
{
	return 1;
}

int const_hihi(int p)
	requires p <^ @Hi
	ensures res <^ @Hi;
{
	return 1;
}

bool bool_const_lo()
	requires true
	ensures res <^ @Lo;
{
	return true;
}

bool bool_const_hi()
	requires true
	ensures res <^ @Hi;
{
	return true;
}

bool bool_const_lolo(bool p)
	requires p <^ @Lo
	ensures res <^ @Lo;
{
	return true;
}

bool bool_const_lohi(bool p)
	requires p <^ @Lo
	ensures res <^ @Hi;
{
	return true;
}

bool bool_const_hilo(bool p)
	requires p <^ @Hi
	ensures res <^ @Lo;
{
	return true;
}

bool bool_const_hihi(bool p)
	requires p <^ @Hi
	ensures res <^ @Hi;
{
	return true;
}

