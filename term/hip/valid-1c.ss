int foo (int x)
 case {
	x<0 -> ensures false;
	x=0 -> ensures res=0;
	x>0 -> ensures res=2*x;
 }
{
	if (x==0)
		return 0;
	else
		return 2+foo(x-1);
}

/*
TODO : Is it necessary to highlight unreachable state?
Termination checking result:
valid-1c.ss_11_11: Unreachable state.
*/
