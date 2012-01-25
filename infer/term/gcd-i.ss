ranking r(int x, int y).

int gcd (int x, int y)
infer [r] 
requires x>0 & y>0
case {
  x=y -> requires Term[] ensures true;
  x!=y -> requires Term[r(x,y)] ensures true;
}

{
	if (x>y) 
		return gcd (x-y, y);
	else if (x<y)
		return gcd (x, y-x);
	else
		return x;
}
