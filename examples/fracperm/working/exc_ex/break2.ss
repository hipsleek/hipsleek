int v(int i)
requires i=3
ensures res=2;
{
	int j=5;
	int k=3;
	b1: while(true)
	{
	 if (k>1)
		while(true)
		requires true
		ensures k'=k-1&flow __break_b1;
		{
			k--;
			continue b1;
		}
	if (k!=1) continue b1;
		else break b1;			
	} 
	return i-j;
}
