//logical int p1,p2,p3;

int gcd (int x, int y)
 case {
  x=y -> requires Term[] ensures res=x;
  x!=y ->
  case{
    x>0 & y>0 -> requires Term[x+y] ensures res>0;
   x>0 & y<=0 -> requires Loop ensures false;
   x<=0 & y>0 -> requires Loop ensures false;
   x<=0 & y<=0 -> requires Loop ensures false;
  }
 }
{
	if (x>y) 
		return gcd (x-y, y);
	else if (x<y)
		return gcd (x, y-x);
	else
		return x;
}
