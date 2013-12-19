int foo (int x)

 requires x<0 or x>=0
 ensures  res=2*x;

 requires x<0 & Loop or x=0 & Term[] or x>0 & Term[x]
 ensures  res=2*x;

/*
# valid-1a-bug.ss

 fail pre + but gave an incorrect non-decreasing message?
 Can we avoid terminating checking if there were other failures
 so user would not be mis-lead?

Termination checking result:  (3)->(20) (MayTerm ERR: not decreasing) Term[29; pv_868] -> Term[29; pv_868]

*/
//ensures  x=0 & res=0 or x>0 & res=2*x;
/*
 ensures x<0 & false or 
 case {
	x<0 -> requires Loop 
           ensures false;
	x=0 -> requires Term[] 
           ensures res=0;
	x>0 -> requires Term[x] 
           ensures res=2*x;
 }
*/
{
	if (x==0)
		return 0;
	else
		return 2+foo(x-1);
}
