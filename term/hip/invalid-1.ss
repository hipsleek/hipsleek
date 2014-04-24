int foo (int x)
 case {
	x<0 -> requires Loop 
           ensures false;
	x=0 -> requires MayLoop
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
TODO : should say ERROR in first line
Termination checking result: 
invalid-1.ss_14_9: Terminating: The given variance is well-founded.
invalid-1.ss_14_11: Terminating: The given variance is well-founded.
invalid-1.ss_14_11: Error: Term->MayLoop transition is invalid.
invalid-1.ss_14_15: Terminating: The given variance is well-founded.
invalid-1.ss_11_5: Terminating: The given variance is well-founded.
invalid-1.ss_14_11: Unreachable state.
*/

