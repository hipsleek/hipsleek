void spring (ref int x0,ref int x1,ref int x2,ref int x3,ref int x4,ref int x5)
requires x0>2 & x1>2 & x2>2 & x3>2 & x4>2 & x5>2
ensures x0'= x0+2 & x1'= x1+2 & x2'= x2+2 & x3'= x3+2 & x4'= x4+2 & x5'= x5+2;
{
	int one= 1;
	int four= 4;
	x0= x0+one;
	x1= x1+one;
	x2= x2+one;
	x3= x3+one;
	x4= x4+one;
	x5= x5+one;
	x0= x0+one;
	x1= x1+one;
	x2= x2+one;
	x3= x3+one;
	x4= x4+one;
	x5= x5+one;
	bool b0= x0>four;
	bool b1= x1>four;
	bool b2= x2>four;
	bool b3= x3>four;
	bool b4= x4>four;
	bool b5= x5>four;
	if (b0)
	{
		x0= x0+one;
		x1= x1+one;
		x2= x2+one;
		x3= x3+one;
		x4= x4+one;
		x5= x5+one;
	if (b1)
	{
		x0= x0-one;
		x1= x1-one;
		x2= x2-one;
		x3= x3-one;
		x4= x4-one;
		x5= x5-one;
	if (b2)
	{
		x0= x0+one;
		x1= x1+one;
		x2= x2+one;
		x3= x3+one;
		x4= x4+one;
		x5= x5+one;
	if (b3)
	{
		x0= x0-one;
		x1= x1-one;
		x2= x2-one;
		x3= x3-one;
		x4= x4-one;
		x5= x5-one;
	if (b4)
	{
		x0= x0+one;
		x1= x1+one;
		x2= x2+one;
		x3= x3+one;
		x4= x4+one;
		x5= x5+one;
	if (b5)
	{
		x0= x0-one;
		x1= x1-one;
		x2= x2-one;
		x3= x3-one;
		x4= x4-one;
		x5= x5-one;
	}
	}
	}
	}
	}
	}
}