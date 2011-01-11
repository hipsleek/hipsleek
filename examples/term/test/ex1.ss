/*
int foo(int x)
//requires x>0
//variance ==> [x<0]
//ensures res=0;
case {
	x<=0 -> ensures true;
	x>0 -> variance ==> [x]
		   ensures true;
}
{
	if (x == 0) return x;
:	else return foo(x-1);
}
*/

int goo(int x)
requires x<=0
ensures false;
requires x>0
//requires x=0
//variance ==> [x<0]
//variance [x@-3] ==> [true & (false | true)]
variance [x] ==> [x=0]
//variance ==> [x>10]
ensures res=0;
{
	if (x == 0) return x;
	else if (x>0) return foo(x-1);
	else return hoo(x-1);
}

int foo(int x)
requires x>0
//requires x=0
//variance ==> [x<0]
//variance [x@-3] ==> [true & (false | true)]
variance [x] ==> [x=0]
//variance ==> [x>10]
ensures res=0;
{
	if (x == 0) return x;
	else return goo(x-1);
}

int hoo(int x)
requires x>0
//requires x=0
//variance ==> [x<0]
//variance [x@-3] ==> [true & (false | true)]
variance [x] ==> [x=0]
//variance ==> [x>10]
ensures res=0;
{
	if (x == 0) return x;
	else return hoo(x-1);
}