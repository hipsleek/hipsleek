int ret (int x)
requires Term
case {
	x=0 -> ensures res=1;
	x!=0 -> ensures res=0;
}
{
	if (x == 0)
		return 1;
	else
		return 0;
}

bool test (int x, int y)
case {
	x!=y -> requires Term ensures res;
	x=y -> requires Loop ensures false;
}
{
	if (x != y)
		return true;
	else
		return test(x-1, y-1);
}

void main ()
requires Term
ensures true;
{
	int x = rand_int() % 2;
	int y = ret(x);
	test(x, y);
}

int rand_int ()
requires Term
ensures true;
