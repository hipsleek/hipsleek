logical int p1,p2,p3;

int gcd (int x, int y)
requires x>0 & y>0
infer[p1,p2,p3]
case {
  x<y -> requires Term[p1,y] ensures true;
	x=y -> requires Term[p2] ensures true;
	x>y -> requires Term[p3,x] ensures true;
}

{
	if (x>y) 
		return gcd (x-y, y);
	else if (x<y)
		return gcd (x, y-x);
	else
		return x;
}
