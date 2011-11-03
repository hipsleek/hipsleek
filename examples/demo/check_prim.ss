int sum(int n)
	requires true 
    ensures res=n; //if n < 0, the function never stops
{
	if (n == 0)
		return n;
	else 
		return 1 + sum(n-1);
}


int sum_loop(int n) 
	requires n>=0 
    ensures res=n;
{
	int i = 0, s = 0;
	while (n > 0) 
      requires n>=0 
      ensures n'+s'=s+n & n'=0;//'
	{
		s++;
        n=n-1;
	}
	return s;
}

