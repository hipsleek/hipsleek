void spring (ref int x0,ref int x1)
requires x0>2 & x1>2
ensures x0'= x0+2 & x1'= x1+2;
{
	int one= 1;
	int four= 4;
	x0= x0+one;
	x1= x1+one;
	x0= x0+one;
	x1= x1+one;
	bool b0= x0>four;
	bool b1= x1>four;
	if (b0)
	{
		x0= x0+one;
		x1= x1+one;
	if (b1)
	{
		x0= x0-one;
		x1= x1-one;
	}
	}
}