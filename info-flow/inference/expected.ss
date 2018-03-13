int input(int x)
  requires x <^ @Hi
  ensures res <^ @Hi;

int output(int x)
  requires x <^ @Lo
  ensures true;


data C {
	int x;
}


/*int id1(int x)
  requires forall (sec_a: x <^ a)
  ensures res <^ a;
{
  return x;
}*/

int id2(int x)
  requires x <^ @Lo
  ensures res <^ @Lo;
  requires x <^ @Hi
  ensures res <^ @Hi;
{
  return x;
}

int double_if(int x)
  requires x <^ @Hi
  ensures res <^ @Hi;
{
  input(x);
  int y = 0;
  int z = 0;
  if(x == 0) {
    y = 1;
  }
  if(y == 0) {
    z = 1;
  }
  dprint;
  return z;
}

int assign1()
	requires true
	ensures res <^ @Lo;
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

int assign6(int p)
	requires p <^ @Hi
	ensures res <^ @Hi;
{
  input(p);
	int x = p;
	return x;
}

bool binary1(int x, int y)
	requires x <^ @Lo & y <^ @Lo
	ensures res <^ @Lo;
{
	return (x == y);
}

bool binary6(int x, int y)
	requires x <^ @Lo & y <^ @Hi
	ensures res <^ @Hi;
{
  input(y);
	return (x == y);
}

bool binary7(int x, int y)
	requires x <^ @Hi & y <^ @Lo
	ensures res <^ @Hi;
{
  input(x);
	return (x == y);
}

bool binary8(int x, int y)
	requires x <^ @Hi & y <^ @Hi
	ensures res <^ @Hi;
{
  input(x);
  input(y);
	return (x == y);
}

int const_lo()
	requires true
	ensures res <^ @Lo;
{
	return 1;
}

int single_if(int x)
  requires x <^ @Hi
  ensures res <^ @Hi;
{
  input(x);
  int y = 0;
  if(x == 0) {
    dprint;
    y = 1;
  }
  return y;
}

int rec2a(int x)
	requires x <^ @Lo
	ensures res <^ @Lo;
{
	return rec2a(x);
}

int rec2b(int x)
	requires x <^ @Lo
	ensures res <^ @Lo;
{
	return rec2b(x);
}

int rec3a(int x)
	requires x <^ @Hi
	ensures res <^ @Hi;
{
  input(x);
	return rec3a(x);
}

int rec3b(int x)
	requires x <^ @Hi
	ensures res <^ @Hi;
{
  input(x);
	return rec3b(x);
}

int func_id_const1()
	requires true
	ensures res <^ @Lo;
{
	int v = 1;
	return id2(v);
}

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
	requires x <^ @Hi
	ensures res <^ @Hi;
{
  input(x);
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

int if_var4(int x, int y)
	requires x <^ @Hi & y <^ @Lo
	ensures res <^ @Hi;
{
  input(x);
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
  input(y);
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
  input(x);
  input(y);
	int z;
	if (x == 0) {
		z = y;
	}
	else {
		z = 0;
	}

	return z;
}

int obj_var1(int b)
	requires b <^ @Lo
	ensures res <^ @Lo;
{
	C c = new C(b);
	return c.x;
}

int obj_var4(int b)
	requires b <^ @Hi
	ensures res <^ @Hi;
{
  input(b);
	C c = new C(b);
	return c.x;
}

C obj_var5(int b)
	requires b <^ @Lo
	ensures res <^ @Lo;
{
	C c = new C(b);
	return c;
}

C obj_var6(int b)
	requires b <^ @Hi
	ensures res <^ @Hi;
{
  input(b);
	C c = new C(b);
	return c;
}
