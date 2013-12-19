int foo (int x)
 requires x<0 & Loop or x=0 & Term[] or x>0 & Term[x]
//ensures  res=2*x;
 ensures  x=0 & res=0 or x>0 & res=2*x;
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
