/********************************************************
Example from VCC testsuite: termination-missing-is-top
*********************************************************/

int f (int a)
case {
	a < 0 -> requires Term ensures true;
	a >= 0 -> requires Term[2*a+1] ensures true;
}
{
	if (a < 0)
		return 0;
	else
		return f(a - 1) + g(a, a + a);
}

int g (int a, int b)
case {
	a < 0 -> requires Term ensures true;
	a >= 0 -> case {
		b < 0 -> requires Term[2*a] ensures true;
		b >= 0 -> requires Term[2*a, b] ensures true;
	}
}
{
	if (a < 0)
		return 0;
	else {
		if (b < 0)
			return f(a - 1);
		else
			return f(a - 1) + g(a, b - 1);
	}
}

/*
VCC example uses the measures [a] and [a, b] for
f and g, respectively; but they are not decreasing
with the transition f->g
*/
