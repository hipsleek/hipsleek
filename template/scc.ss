template int r1(int x).
template int r2(int y).

void f (int x) 
infer[r1]
case {
	x<0 -> requires Term ensures true;
	x>=0 -> requires Term[r1(x)] ensures true;
}
{
	if (x < 0) return;
	else return g(x);
}

void g (int y)
infer[r2]
requires y>=0 & Term[r2(y)]
ensures true;
{
	return f(y-1);
}
