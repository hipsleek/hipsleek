void spring (ref int x0, ref int x1, ref int x2, ref int x3, ref int x4, ref int x5, ref int x6, ref int x7)
requires x0>2 & x1>2 & x2>2 & x3>2 & x4>2 & x5>2 & x6>2 & x7>2
ensures x0' = x0+2 & x1' = x1+2 & x2' = x2+2 & x3' = x3+2 & x4' = x4+2 & x5' = x5+2 & x6' = x6+2 & x7' = x7+2;
{
	x0= x0+1;
	x1= x1+1;
	x2= x2+1;
	x3= x3+1;
	x4= x4+1;
	x5= x5+1;
	x6= x6+1;
	x7= x7+1;
	x0= x0+1;
	x1= x1+1;
	x2= x2+1;
	x3= x3+1;
	x4= x4+1;
	x5= x5+1;
	x6= x6+1;
	x7= x7+1;
	bool b0= x0>4;
	bool b1= x1>4;
	bool b2= x2>4;
	bool b3= x3>4;
	bool b4= x4>4;
	bool b5= x5>4;
	bool b6= x6>4;
	bool b7= x7>4;
	 if (b0)
	{
		x0= x0+1;
		x1= x1+1;
		x2= x2+1;
		x3= x3+1;
		x4= x4+1;
		x5= x5+1;
		x6= x6+1;
		x7= x7+1;
	 if (b1)
	{
		x0= x0-1;
		x1= x1-1;
		x2= x2-1;
		x3= x3-1;
		x4= x4-1;
		x5= x5-1;
		x6= x6-1;
		x7= x7-1;
	 if (b2)
	{
		x0= x0+1;
		x1= x1+1;
		x2= x2+1;
		x3= x3+1;
		x4= x4+1;
		x5= x5+1;
		x6= x6+1;
		x7= x7+1;
	 if (b3)
	{
		x0= x0-1;
		x1= x1-1;
		x2= x2-1;
		x3= x3-1;
		x4= x4-1;
		x5= x5-1;
		x6= x6-1;
		x7= x7-1;
	 if (b4)
	{
		x0= x0+1;
		x1= x1+1;
		x2= x2+1;
		x3= x3+1;
		x4= x4+1;
		x5= x5+1;
		x6= x6+1;
		x7= x7+1;
	 if (b5)
	{
		x0= x0-1;
		x1= x1-1;
		x2= x2-1;
		x3= x3-1;
		x4= x4-1;
		x5= x5-1;
		x6= x6-1;
		x7= x7-1;
	 if (b6)
	{
		x0= x0+1;
		x1= x1+1;
		x2= x2+1;
		x3= x3+1;
		x4= x4+1;
		x5= x5+1;
		x6= x6+1;
		x7= x7+1;
	 if (b7)
	{
		x0= x0-1;
		x1= x1-1;
		x2= x2-1;
		x3= x3-1;
		x4= x4-1;
		x5= x5-1;
		x6= x6-1;
		x7= x7-1;
	}
	}
	}
	}
	}
	}
	}
	}
}