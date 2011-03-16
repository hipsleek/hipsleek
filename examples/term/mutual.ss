int f (int x)
case {
	x > 10 -> variance (2) [x] ensures true;
	x <= 10 -> case {
					x < 0 -> variance (0) ensures true;
					x >= 0 -> variance (1) [2*x+3] ensures true;
			   }
}
{
	if (x > 10)
	   return f(x - 1);
	else
		if (x < 0)
			return 0;
		else
			return g(x + 1);
}

int g (int x)
case {
	x > 5 -> variance (2) [x] ensures true;
	x <= 5 -> case {
					x < 0 -> variance (0) ensures true;
					x >= 0 -> variance (1) [2*x] ensures true;
			   }
}
{
	if (x > 5)
	   return g(x - 1);
	else
		if (x < 0)
			return 0;
		else
			return f(x - 1);
}
