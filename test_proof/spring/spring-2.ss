void spring (ref int x0, ref int x1)
requires x0>2 & x1>2
ensures x0' = x0+2 & x1' = x1+2;
{
	x0= x0+1;
	x1= x1+1;
	x0= x0+1;
	x1= x1+1;
	bool b0= x0>4;
	bool b1= x1>4;
	 if (b0)
	{
		x0= x0+1;
		x1= x1+1;
	 if (b1)
	{
		x0= x0-1;
		x1= x1-1;
	}
	}
}