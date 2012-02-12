int incr (int i)
requires Term
ensures res = i + 1;
{
	return i + 1;
}

int incr2 (int i)
requires Term
ensures res = i + 2;
{
	return i + 2;
}

int incr3 (int i)
requires Term
ensures res = i + 3;
{
	return i + 3;
}

int add (int n)
requires Term 
ensures true;
{
	int r = 0;
	int i = 0;
	while (i <= n)
	case {
		i>n -> requires Term ensures true;
		i<=n -> requires Term[n-i] ensures true;
	}
	{
		r = r + i;
		i = incr(i);
	}
	return r;
}

int add2 (int n)
requires Term 
ensures true;
{
	int r = 0;
	int i = 0;
	while (i <= n)
	case {
		i>n -> requires Term ensures true;
		i<=n -> requires Term[n-i] ensures true;
	}
	{
		r = r + i;
		i = incr2(i);
	}
	return r;
}

int add3 (int n)
requires Term 
ensures true;
{
	int r = 0;
	int i = 0;
	while (i <= n)
	case {
		i>n -> requires Term ensures true;
		i<=n -> requires Term[n-i] ensures true;
	}
	{
		r = r + i;
		i = incr3(i);
	}
	return r;
}
