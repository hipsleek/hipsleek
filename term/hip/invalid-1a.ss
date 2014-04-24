int foo (int x)
 case {
	x<0 -> requires Loop 
           ensures true; /* poststate of Loop must be unreachable */
	x=0 -> requires Term[0]
           ensures res=0;
	x>0 -> requires Term[x] 
           ensures res=2*x;
 }
{
	if (x==0)
		return 0;
	else
		return 2+foo(x-1);
}
/*
TODO : should fail due to detect LOOP.
*/

