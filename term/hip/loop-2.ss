// TODO: this example should result in a Loop unsoundness error?

int foo (int x)
 case {
    x<0 -> requires Loop
           ensures false;
	x=0 -> requires Term[0] 
           ensures res=0; /* poststate of Loop must be unreachable */
	x>0 -> requires MayLoop 
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

