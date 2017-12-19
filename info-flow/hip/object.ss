data C {
	int x;
}

int obj_const1()
	requires true
	ensures res <^ @Lo;
{
	C c = new C(1);
	return c.x;
}

int obj_const2()
	requires true
	ensures res <^ @Hi;
{
	C c = new C(1);
	return c.x;
}


int obj_var1(int b)
	requires b <^ @Lo
	ensures res <^ @Lo;
{
	C c = new C(b);
	return c.x;
}

int obj_var2(int b)
	requires b <^ @Lo
	ensures res <^ @Hi;
{
	C c = new C(b);
	return c.x;
}

int obj_var3_fails(int b)
	requires b <^ @Hi
	ensures res <^ @Lo;
{
	C c = new C(b);
	return c.x;
}

int obj_var4(int b)
	requires b <^ @Hi
	ensures res <^ @Hi;
{
	C c = new C(b);
	return c.x;
}