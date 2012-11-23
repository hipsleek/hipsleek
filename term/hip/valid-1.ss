int foo (int x)
 case {
	x<0 -> requires Loop 
           ensures false;
	x=0 -> requires Term[] 
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
TODO : where is the Loop -> Loop scenario
It is hard to see which transitions are being checked.
I wonder if it is possible to write something like
  (OK) Loop  --> Loop
  (OK) Term[x] --> Term[]
  (OK) Term[x] & x=y+1 --> Term[y] 
  (ERR) Term[x] & x=y+1 --> MayLoop 
instead of the vague "The given variace is well-founded".

Termination checking result:
valid-1.ss_14_9: Terminating: The given variance is well-founded.
valid-1.ss_14_9: Terminating: The given variance is well-founded.
valid-1.ss_14_11: Terminating: The given variance is well-founded.
valid-1.ss_14_11: Terminating: The given variance is well-founded.
valid-1.ss_14_15: Terminating: The given variance is well-founded.
valid-1.ss_11_5: Terminating: The given variance is well-founded.
valid-1.ss_14_11: Unreachable state.
valid-1.ss_11_5: Terminating: The given variance is well-founded.
*/
