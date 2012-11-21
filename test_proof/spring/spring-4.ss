void spring (ref int x0, ref int x1, ref int x2, ref int x3)
requires x0>2 & x1>2 & x2>2 & x3>2
ensures x0' = x0+2 & x1' = x1+2 & x2' = x2+2 & x3' = x3+2;
{
	x0= x0+1;
	x1= x1+1;
	x2= x2+1;
	x3= x3+1;
	x0= x0+1;
	x1= x1+1;
	x2= x2+1;
	x3= x3+1;
	bool b0= x0>4;
	bool b1= x1>4;
	bool b2= x2>4;
	bool b3= x3>4;
	 if (b0)
	{
		x0= x0+1;
		x1= x1+1;
		x2= x2+1;
		x3= x3+1;
	 if (b1)
	{
		x0= x0-1;
		x1= x1-1;
		x2= x2-1;
		x3= x3-1;
	 if (b2)
	{
		x0= x0+1;
		x1= x1+1;
		x2= x2+1;
		x3= x3+1;
	 if (b3)
	{
		x0= x0-1;
		x1= x1-1;
		x2= x2-1;
		x3= x3-1;
	}
	}
	}
	}
}