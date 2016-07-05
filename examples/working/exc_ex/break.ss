

int loop (int i)
requires i=10 
ensures res = 3;
{
	test:while (true)
	requires i>=3
	ensures  i'=3;
	{
		if (i==3) break test;
			else i--;
	}
	return i;

}
