void spring (ref int x0, ref int x1, ref int x2)
requires x0>2 & x1>2 & x2>2
ensures x0' = x0+3 & x1' = x1+3 & x2' = x2+3;
{
	x0= x0+1;
	x1= x1+1;
	x2= x2+1;
	x0= x0+1;
	x1= x1+1;
	x2= x2+1;
	bool b0= x0>4;
	bool b1= x1>4;
	bool b2= x2>4;
	 if (b0)
	{
		x0= x0+1;
		x1= x1+1;
		x2= x2+1;
	 if (b1)
	{
		x0= x0-1;
		x1= x1-1;
		x2= x2-1;
	 if (b2)
	{
		x0= x0+1;
		x1= x1+1;
		x2= x2+1;
	}
	}
	}
}