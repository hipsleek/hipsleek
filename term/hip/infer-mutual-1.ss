logical int p1, p2, p3, p4, p5, p6, p7, p8;

int f (int x)
infer[p1, p2, p5, p6]
case {
	x<=0 -> requires Term[p5] ensures res=0;
	x>0 -> requires Term[p1, 2*x] ensures res=3*x;
}
{
	if (x <= 0)
		return 0;
	else
		return 1 + g(x);
}

int g (int x)
infer[p1, p2, p5, p6]
case {
	x<=0 -> requires Term[p6]  ensures res=0;
	x>0 -> requires Term[p2, 2*x-1] ensures res=3*x-1;
}
{
	if (x <= 0)
		return 0;
  else
		return 2 + f(x-1);
}


int m (int x)
infer[p3, p4, p7, p8]
case {
	x>10 -> requires Term[p3, x] ensures true;
	x<=10 -> requires Term[p7] ensures res=3*x-1 or res=0;
}
{
	if (x>10)
		return n(x-1);
	else
		return g(x);
}

int n (int x)
infer[p3, p4, p7, p8]
case {
	x>5 -> requires Term[p4, x] ensures true;
	x<=5 -> requires Term[p8] ensures res=3*x or res=0;
}
{
	if (x>5)
		return m(x-1);
	else
		return f(x);
}
