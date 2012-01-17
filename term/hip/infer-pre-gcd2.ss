//Example used in CAV'08 - Proving conditional termination
//Infer the precondition for termination

logical int p1,p2,p3;

int gcd (int x, int y)
//requires x>0 & y>0
/*
//infer[x,y] //=> x>=1 & y>=1
case {
	x<y -> requires Term[y] ensures true;
	x=y -> requires Term[] ensures true;
	x>y -> requires Term[x] ensures true;
}
*/
/*
TODO : too strong?
!!! Inferred Heap :[]
!!! Inferred Pure :[ 1<=x, pv_630<=p1, p2<=p1, (1+y)<=(2*x), (1+x)<=y]
!!! Inferred Heap :[]
!!! Inferred Pure :[ p1<=p2, (1+x)<=(2*y), (1+y)<=x, pv_630<=p2, 1<=y]
*/
//requires x>0 & y>0
infer[x, y]
case {
  x<y -> requires Term[0,y] ensures true;
  x=y -> requires Term ensures true;
	x>y -> requires Term[0,x] ensures true;
}
{
	if (x>y) 
		return gcd (x-y, y);
	else if (x<y)
		return gcd (x, y-x);
	else
		return x;
}
