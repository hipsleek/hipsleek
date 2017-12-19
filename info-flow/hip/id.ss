int id_int_lolo(int x)
	requires x <^ @Lo
	ensures res <^ @Lo;
{
	return x;
}

int id_int_lohi(int x)
	requires x <^ @Lo
	ensures res <^ @Hi;
{
	return x;
}

int id_int_hilo_fail(int x)
	requires x <^ @Hi
	ensures res <^ @Lo;
{
	return x;
}

int id_int_hihi(int x)
	requires x <^ @Hi
	ensures res <^ @Hi;
{
	return x;
}

bool id_bool_lolo(bool x)
	requires x <^ @Lo
	ensures res <^ @Lo;
{
	return x;
}

bool id_bool_lohi(bool x)
	requires x <^ @Lo
	ensures res <^ @Hi;
{
	return x;
}

bool id_bool_hilo_fail(bool x)
	requires x <^ @Hi
	ensures res <^ @Lo;
{
	return x;
}

bool id_bool_hihi(bool x)
	requires x <^ @Hi
	ensures res <^ @Hi;
{
	return x;
}