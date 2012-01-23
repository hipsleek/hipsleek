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
//requires x>0 & y>0
/*
infer[p1,p2,p3, x, y]
case {
  x<y -> requires Term[p1,y] ensures true;
  x=y -> requires Term ensures true;
	x>y -> requires Term[x] ensures true;
}
*/
/* TODO : seems a little strong?
!!! Inferred Heap :[]
!!! Inferred Pure :[ pv_629<=p1, (1+y)<=x, 1<=y, pv_629<=p1, (1+x)<=y, 1<=x]
Answer : inference inferred existing state like x>y and x<y which leads
to false. The new version in infer2 should fix this problem.
*/

//requires x>0 & y>0
infer[x, y]
case {
	x=y -> requires Term[0] ensures true;
	x!=y -> requires Term[0, x+y] ensures true;
}

{
	if (x>y) 
		return gcd (x-y, y);
	else if (x<y)
		return gcd (x, y-x);
	else
		return x;
}
