//Example to check the bounded checking
//Can we use infer to make the bounded 
//condition satisfied, e.g. x>=0?

int foo (int x)
 case {
	x=0 -> requires Term[0]
           ensures res=0;
	x!=0 -> requires Term[x] 
           ensures res=2*x;
 }
{
	if (x==0)
		return 0;
	else
		return 2+foo(x-1);
}


